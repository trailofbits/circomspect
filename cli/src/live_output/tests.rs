// This subprocess test deliberately panics on setup or assertion failures.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::panic, clippy::unwrap_used)]

use std::collections::HashSet;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

use program_analysis::application::{analyze_files_with_observer, AnalysisObserver, AnalysisProgress};
use program_structure::constants::Curve;
use program_structure::file_definition::FileLibrary;
use program_structure::report::{MessageCategory, Report, ReportLabel};
use program_structure::writers::{ReportWriteError, StdoutWriter};

use crate::live_output::LiveOutput;
use crate::progress;

const CHILD_SOURCE: &str = "CIRCOMSPECT_TEST_STREAM_SOURCE";

struct PausingOutput<'a>(LiveOutput<'a>);

impl AnalysisObserver for PausingOutput<'_> {
    fn progress(&mut self, event: AnalysisProgress<'_>) -> io::Result<()> {
        self.0.progress(event)?;
        if let AnalysisProgress::AnalyzingTemplate("Later") = event {
            io::stdin().read_exact(&mut [0])?;
        }
        Ok(())
    }

    fn report(&mut self, report: &Report, files: &FileLibrary) -> Result<(), ReportWriteError> {
        self.0.report(report, files)
    }

    fn additional_call_paths(
        &mut self,
        report: &Report,
        locations: &[ReportLabel],
        files: &FileLibrary,
    ) -> Result<(), ReportWriteError> {
        self.0.additional_call_paths(report, locations, files)
    }
}

fn blocked_analysis(source: &Path) {
    let mut writer = StdoutWriter::new(false);
    let ignored = HashSet::new();
    progress::report(false, |progress| {
        let output = LiveOutput::new(progress, &mut writer, MessageCategory::Warning, &ignored);
        analyze_files_with_observer(
            &[source.to_owned()],
            &[],
            Curve::Bn254,
            program_analysis::application::AnalysisTimeout::Unlimited,
            &mut PausingOutput(output),
        )
    })
    .unwrap();
}

#[test]
fn diagnostics_arrive_while_later_analysis_is_blocked() {
    if let Some(source) = std::env::var_os(CHILD_SOURCE) {
        blocked_analysis(Path::new(&source));
        return;
    }
    let source =
        std::env::temp_dir().join(format!("circomspect-live-{}.circom", std::process::id()));
    std::fs::write(
        &source,
        "pragma circom 2.2.3;\n\
        template Early(){var dead=1;signal output out;out<==0;}\n\
        template Later(){signal output out;out<==1;}",
    )
    .unwrap();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "live_output::tests::diagnostics_arrive_while_later_analysis_is_blocked",
            "--nocapture",
        ])
        .env(CHILD_SOURCE, &source)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let stdout = child.stdout.take().unwrap();
    let (sent, received) = mpsc::channel();
    let reader = std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines() {
            let line = line.unwrap();
            if line.contains("warning: Assigned value of `dead`") {
                sent.send(line).unwrap();
            }
        }
    });
    let warning = received.recv_timeout(Duration::from_secs(3));
    let running = child.try_wait().unwrap().is_none();
    if running {
        if warning.is_ok() {
            child.stdin.take().unwrap().write_all(&[1]).unwrap();
        } else {
            child.kill().unwrap();
        }
    }
    let result = child.wait_with_output().unwrap();
    reader.join().unwrap();
    std::fs::remove_file(source).unwrap();
    assert!(warning.is_ok(), "no warning reached the pipe while analysis was paused");
    assert!(running, "the warning must precede analysis completion");
    assert!(result.status.success(), "{:?}", result.stderr);
}
