// Assertions and fixture setup intentionally fail the test on errors.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]
#![cfg(unix)]

use std::io::{BufRead, BufReader};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

#[test]
fn reports_progress_before_waiting_for_source_input() {
    let directory =
        std::env::temp_dir().join(format!("circomspect-progress-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("waiting.circom");
    assert!(Command::new("mkfifo").arg(&source).status().unwrap().success());
    let mut child = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(&source)
        .args(["-l", "INFO"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let stdout = child.stdout.take().unwrap();
    let (sender, receiver) = mpsc::channel();
    let reader = std::thread::spawn(move || {
        let mut line = String::new();
        let result = BufReader::new(stdout).read_line(&mut line).map(|_| line);
        sender.send(result).unwrap();
    });
    let first_line = receiver.recv_timeout(Duration::from_secs(5));
    let running = child.try_wait().unwrap().is_none();
    // Closing the blocked process before assertions also cleans up a failing regression.
    if running {
        child.kill().unwrap();
    }
    child.wait().unwrap();
    reader.join().unwrap();
    std::fs::remove_file(source).unwrap();
    std::fs::remove_dir(directory).unwrap();
    assert!(running, "the analyzer must still be waiting for the source");
    assert_eq!(
        first_line.expect("no progress while the source read was blocked").unwrap(),
        "circomspect: loading input files\n"
    );
}
