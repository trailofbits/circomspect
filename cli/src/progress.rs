use std::io;
use std::sync::mpsc::{self, Receiver, RecvTimeoutError, Sender, SyncSender};
use std::thread;
use std::time::{Duration, Instant};

use program_analysis::application::{AnalysisProgress, ApplicationError};
use program_structure::writers::{LogWriter, StdoutWriter};

#[cfg(test)]
mod tests;

const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(5);

struct Stage {
    message: String,
    acknowledged: SyncSender<io::Result<()>>,
}

pub(super) struct ProgressReporter {
    stages: Sender<Stage>,
}

impl ProgressReporter {
    pub(super) fn stage(&self, progress: AnalysisProgress<'_>) -> io::Result<()> {
        let (acknowledged, acknowledgment) = mpsc::sync_channel(0);
        self.stages
            .send(Stage { message: progress_message(progress), acknowledged })
            .map_err(|_| reporter_stopped())?;
        acknowledgment.recv().map_err(|_| reporter_stopped())?
    }
}

pub(super) fn report<T>(
    verbose: bool,
    work: impl FnOnce(&ProgressReporter) -> Result<T, ApplicationError>,
) -> Result<T, ApplicationError> {
    report_with(
        HEARTBEAT_INTERVAL,
        move || {
            let mut writer = StdoutWriter::new(verbose);
            move |message: &str| writer.write_message(message)
        },
        work,
    )
}

fn report_with<T, W>(
    interval: Duration,
    make_writer: impl FnOnce() -> W + Send,
    work: impl FnOnce(&ProgressReporter) -> Result<T, ApplicationError>,
) -> Result<T, ApplicationError>
where
    W: FnMut(&str) -> io::Result<()>,
{
    thread::scope(|scope| {
        let (stages, receiver) = mpsc::channel();
        let reporter = ProgressReporter { stages };
        let worker = scope.spawn(move || report_stages(&receiver, interval, make_writer()));
        let result = work(&reporter);
        drop(reporter);
        let completed = match worker.join() {
            Ok(Ok(())) => Ok(()),
            Ok(Err(error)) => Err(ApplicationError::Progress(error)),
            Err(_) => Err(ApplicationError::Progress(io::Error::other(
                "analysis progress reporter panicked",
            ))),
        };
        if let Err(ApplicationError::Output(_)) = &result {
            return result;
        }
        completed.and(result)
    })
}

fn report_stages(
    stages: &Receiver<Stage>,
    interval: Duration,
    mut write: impl FnMut(&str) -> io::Result<()>,
) -> io::Result<()> {
    let mut current: Option<(String, Instant)> = None;
    loop {
        match stages.recv_timeout(interval) {
            Ok(stage) => {
                let result = write(&stage.message);
                let failed = result.is_err();
                if stage.acknowledged.send(result).is_err() || failed {
                    return Ok(());
                }
                current = Some((stage.message, Instant::now()));
            }
            Err(RecvTimeoutError::Timeout) => {
                if let Some((message, started)) = &current {
                    write(&format!("still {message} ({}s elapsed)", started.elapsed().as_secs()))?;
                }
            }
            Err(RecvTimeoutError::Disconnected) => return Ok(()),
        }
    }
}

fn reporter_stopped() -> io::Error {
    io::Error::new(io::ErrorKind::BrokenPipe, "analysis progress reporter stopped")
}

fn progress_message(progress: AnalysisProgress<'_>) -> String {
    match progress {
        AnalysisProgress::LoadingSources => "loading input files".into(),
        AnalysisProgress::LiftingSources => "resolving source definitions".into(),
        AnalysisProgress::IndexingProject => "preparing analysis".into(),
        AnalysisProgress::AnalyzingFunction(name) => format!("analyzing function '{name}'"),
        AnalysisProgress::AnalyzingTemplate(name) => format!("analyzing template '{name}'"),
        AnalysisProgress::AnalyzingBus(name) => format!("analyzing bus '{name}'"),
    }
}
