// Tests intentionally fail by panicking; subprocess assertions preserve crash evidence.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::panic, clippy::unwrap_used)]

use std::io::Write;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use circomspect_parser::hir::lift_project;
use circomspect_parser::frontend::{
    parse_source, DiagnosticKind, Item, LoadedProject, SourceFile, SourceId, Statement, Version,
    VersionPolicy, WalkSyntax,
};

const WORKER_CASE: &str = "CIRCOMSPECT_GRAMMAR_DEPTH_CASE";

fn run_worker(case: &str) {
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "grammar_depth_worker", "--nocapture"])
        .env(WORKER_CASE, case)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > Duration::from_secs(10) {
            child.kill().unwrap();
            let output = child.wait_with_output().unwrap();
            panic!("depth worker timed out: {case}: {output:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{case}: {output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    for marker in ["parsed and validated", "dropped source"] {
        assert!(stdout.contains(marker), "{case}: missing {marker}: {stdout}");
    }
    if !case.starts_with("parse:") {
        assert!(stdout.contains("walked source"), "{case}: {stdout}");
    }
    if case.starts_with("lift:") {
        for marker in ["lifted HIR", "dropped HIR"] {
            assert!(stdout.contains(marker), "{case}: missing {marker}: {stdout}");
        }
    }
    assert!(output.stderr.is_empty(), "{case}: {:?}", output.stderr);
}

#[test]
fn successful_and_malformed_expression_depth_floors_survive_all_stages() {
    for shape in ["calls", "binary"] {
        for (mode, depth, stack_mib) in [
            ("parse", 2048, 2),
            ("walk", 1024, 2),
            ("walk", 2048, 4),
            ("lift", 512, 2),
            ("recover", 4096, 2),
            ("segment", 4096, 2),
        ] {
            run_worker(&format!("{mode}:{shape}:{depth}:{stack_mib}"));
        }
    }
}

fn checkpoint(marker: &str) {
    writeln!(std::io::stdout().lock(), "{marker}").unwrap();
}

fn source(mode: &str, shape: &str, depth: usize) -> String {
    let expression = match shape {
        "calls" => format!("{}1{}", "F(".repeat(depth), ")".repeat(depth)),
        "binary" => format!("1{}", "+1".repeat(depth)),
        other => panic!("unknown expression shape: {other}"),
    };
    let body = match mode {
        "parse" | "walk" | "lift" => format!("function T(){{return {expression};}}"),
        "recover" => format!(
            "function T(){{return {expression}+;return 9;}}function Neighbor(){{return 2;}}"
        ),
        "segment" => {
            format!("component main={expression}+;function Neighbor(){{return 2;}}")
        }
        other => panic!("unknown depth mode: {other}"),
    };
    format!("function F(n){{return n;}}{body}")
}

fn assert_recovery(mode: &str, source: &str, parsed: &circomspect_parser::frontend::ParseOutcome) {
    assert_eq!(parsed.diagnostics.len(), 1);
    let diagnostic = &parsed.diagnostics[0];
    assert_eq!(diagnostic.kind, DiagnosticKind::Syntax);
    let span = diagnostic.span().unwrap();
    let end = source.find("+;").unwrap() + 2;
    if mode == "recover" {
        let start = source.find("function T(){").unwrap() + "function T(){".len();
        assert_eq!(span.start()..span.end(), start..end);
        assert_eq!(
            diagnostic.message,
            "invalid statement; parsing continued at the next statement or block boundary"
        );
        let Item::Definition(definition) = &parsed.ast.items[1] else {
            panic!("recovered definition was discarded");
        };
        assert_eq!(definition.body.statements.len(), 2);
        let Statement::Error { .. } = &definition.body.statements[0] else {
            panic!("invalid statement was not retained as Error");
        };
        let Statement::Return { .. } = &definition.body.statements[1] else {
            panic!("following return was discarded");
        };
    } else {
        assert_eq!(span.start()..span.end(), end - 1..end);
        assert_eq!(diagnostic.message, "unexpected token in Circom source");
        let Item::Error { .. } = &parsed.ast.items[1] else {
            panic!("failed main segment was not retained as Error");
        };
    }
    let Some(Item::Definition(neighbor)) = parsed.ast.items.last() else {
        panic!("following definition was discarded");
    };
    assert_eq!(neighbor.name.name, "Neighbor");
}

fn exercise(case: &str) {
    let parts: Vec<_> = case.split(':').collect();
    let [mode, shape, depth, _stack_mib] = parts.as_slice() else {
        panic!("invalid worker case: {case}");
    };
    let depth = depth.parse::<usize>().unwrap();
    let source = source(mode, shape, depth);
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let parsed = parse_source(SourceId::new(0), &source, policy);
    let expected_walk = match *mode {
        "parse" => {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            None
        }
        "walk" | "lift" => {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            Some(2 * depth + 14)
        }
        "recover" => {
            assert_recovery(mode, &source, &parsed);
            Some(21)
        }
        "segment" => {
            assert_recovery(mode, &source, &parsed);
            Some(15)
        }
        other => panic!("unknown depth mode: {other}"),
    };
    checkpoint("parsed and validated");
    if let Some(expected_walk) = expected_walk {
        let mut walked = 0;
        parsed.ast.walk_syntax(None, &mut |_, _, _| walked += 1);
        assert_eq!(walked, expected_walk);
        checkpoint("walked source");
    }
    if *mode == "lift" {
        let loaded = LoadedProject {
            policy,
            diagnostics: Vec::new(),
            files: vec![SourceFile {
                id: SourceId::new(0),
                path: "depth.circom".into(),
                text: source,
                outcome: parsed,
            }],
        };
        let lifted = lift_project(&loaded);
        assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
        assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
        checkpoint("lifted HIR");
        drop(lifted);
        checkpoint("dropped HIR");
        drop(loaded);
    } else {
        drop(parsed);
    }
    checkpoint("dropped source");
}

#[test]
fn grammar_depth_worker() {
    let Ok(case) = std::env::var(WORKER_CASE) else { return };
    let stack_mib = case.rsplit(':').next().unwrap().parse::<usize>().unwrap();
    std::thread::Builder::new()
        .stack_size(stack_mib * 1024 * 1024)
        .spawn(move || exercise(&case))
        .unwrap()
        .join()
        .unwrap();
}
