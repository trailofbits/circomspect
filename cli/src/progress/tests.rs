// Injected I/O failures and panics verify reporter shutdown and error propagation.
#![allow(clippy::allow_attributes, clippy::panic, clippy::unwrap_used)]

use std::io;
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

use program_analysis::application::{AnalysisProgress, ApplicationError};

use crate::progress::report_with;

const INTERVAL: Duration = Duration::from_millis(10);
const DEADLINE: Duration = Duration::from_secs(2);

#[test]
fn heartbeat_continues_while_analysis_waits_and_stops_before_returning() {
    let (written, messages) = mpsc::channel();
    let result = report_with(
        INTERVAL,
        move || {
            move |message: &str| {
                written.send(message.to_owned()).unwrap();
                Ok(())
            }
        },
        |reporter| {
            reporter.stage(AnalysisProgress::AnalyzingTemplate("Slow"))?;
            assert_eq!(messages.recv_timeout(DEADLINE).unwrap(), "analyzing template 'Slow'");
            let heartbeat = messages.recv_timeout(DEADLINE).map_err(io::Error::other)?;
            assert!(heartbeat.starts_with("still analyzing template 'Slow' ("), "{heartbeat}");
            assert!(heartbeat.ends_with("s elapsed)"), "{heartbeat}");
            Ok(())
        },
    );
    assert!(result.is_ok(), "{result:?}");
    for message in messages.try_iter() {
        assert!(message.starts_with("still analyzing template 'Slow' ("));
    }
    assert_eq!(messages.recv_timeout(DEADLINE), Err(RecvTimeoutError::Disconnected));
}

#[test]
fn stage_failure_reaches_the_callback_before_work_starts() {
    let result = report_with(
        INTERVAL,
        || |_: &str| Err(io::Error::from_raw_os_error(28)),
        |reporter| {
            let error = reporter.stage(AnalysisProgress::LoadingSources).unwrap_err();
            assert_eq!(error.raw_os_error(), Some(28));
            Err::<(), _>(ApplicationError::Progress(error))
        },
    );
    let Err(ApplicationError::Progress(error)) = result else { panic!("expected I/O error") };
    assert_eq!(error.raw_os_error(), Some(28));
}

#[test]
fn heartbeat_failure_wins_over_a_later_disconnected_callback() {
    let (failed, failure) = mpsc::sync_channel(0);
    let result = report_with(
        INTERVAL,
        move || {
            move |message: &str| {
                if message.starts_with("still ") {
                    failed.send(()).unwrap();
                    Err(io::Error::from_raw_os_error(28))
                } else {
                    Ok(())
                }
            }
        },
        |reporter| {
            reporter.stage(AnalysisProgress::LoadingSources)?;
            failure.recv_timeout(DEADLINE).map_err(io::Error::other)?;
            reporter.stage(AnalysisProgress::LiftingSources)?;
            Ok(())
        },
    );
    let Err(ApplicationError::Progress(error)) = result else { panic!("expected I/O error") };
    assert_eq!(error.raw_os_error(), Some(28));
}

#[test]
fn fast_stages_keep_their_messages_and_do_not_emit_a_final_heartbeat() {
    let (written, messages) = mpsc::channel();
    let result = report_with(
        Duration::from_secs(60),
        move || {
            move |message: &str| {
                written.send(message.to_owned()).unwrap();
                Ok(())
            }
        },
        |reporter| {
            reporter.stage(AnalysisProgress::LoadingSources)?;
            reporter.stage(AnalysisProgress::LiftingSources)?;
            Ok(17)
        },
    );
    assert_eq!(result.unwrap(), 17);
    assert_eq!(
        messages.into_iter().collect::<Vec<_>>(),
        ["loading input files", "resolving source definitions",]
    );
}

#[test]
fn a_panicked_reporter_returns_an_actionable_error() {
    let result = report_with(
        INTERVAL,
        || |_: &str| -> io::Result<()> { panic!("writer failed") },
        |reporter| {
            reporter.stage(AnalysisProgress::LoadingSources)?;
            Ok(())
        },
    );
    let Err(ApplicationError::Progress(error)) = result else { panic!("expected reporter error") };
    assert_eq!(error.to_string(), "analysis progress reporter panicked");
}

#[test]
fn panicking_analysis_stops_the_reporter_before_unwinding() {
    let (written, messages) = mpsc::channel();
    let result = std::panic::catch_unwind(|| {
        report_with(
            Duration::from_secs(60),
            move || {
                move |message: &str| {
                    written.send(message.to_owned()).unwrap();
                    Ok(())
                }
            },
            |reporter| -> Result<(), ApplicationError> {
                reporter.stage(AnalysisProgress::LoadingSources)?;
                panic!("analysis failed");
            },
        )
    });
    assert!(result.is_err());
    assert_eq!(messages.recv_timeout(DEADLINE).unwrap(), "loading input files");
    assert_eq!(messages.recv_timeout(DEADLINE), Err(RecvTimeoutError::Disconnected));
}
