//! Peak resident memory for the same end-to-end workloads as the timing benchmark.

use std::collections::BTreeMap;
use std::env;
use std::error::Error;
use std::fs;
use std::hint::black_box;
use std::io::{self, ErrorKind, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use circomspect_program_analysis::application::analyze_files;
use program_structure::constants::Curve;
use serde_json::{json, Value};

mod support;

const SAMPLES: usize = 3;
const MAX_INCREASE_PERCENT: u64 = 5;

enum Mode {
    Measure,
    Save(PathBuf),
    Compare(PathBuf),
    Worker(PathBuf),
}

struct Sample {
    median: u64,
    minimum: u64,
    maximum: u64,
}

fn main() -> Result<(), Box<dyn Error>> {
    match parse_mode()? {
        Mode::Worker(path) => run_worker(&path),
        mode => run_benchmark(mode),
    }
}

fn parse_mode() -> io::Result<Mode> {
    let arguments: Vec<_> =
        env::args_os().skip(1).filter(|argument| argument.to_str() != Some("--bench")).collect();
    match arguments.as_slice() {
        [] => Ok(Mode::Measure),
        [flag, path] if flag.to_str() == Some("--save-baseline") => {
            Ok(Mode::Save(PathBuf::from(path)))
        }
        [flag, path] if flag.to_str() == Some("--baseline") => {
            Ok(Mode::Compare(PathBuf::from(path)))
        }
        [flag, path] if flag.to_str() == Some("--worker") => Ok(Mode::Worker(PathBuf::from(path))),
        _ => Err(io::Error::new(
            ErrorKind::InvalidInput,
            "usage: cargo bench -p circomspect-program-analysis --bench memory -- \
             [--save-baseline FILE | --baseline FILE]",
        )),
    }
}

fn run_benchmark(mode: Mode) -> Result<(), Box<dyn Error>> {
    let executable = env::current_exe()?;
    let mut peaks = BTreeMap::new();
    let mut output = io::stdout().lock();
    for (name, path) in support::fixture_paths() {
        let sample = measure_workload(&executable, &path)?;
        writeln!(
            output,
            "{name}: {} MiB median peak RSS ({}–{} MiB across {SAMPLES} runs)",
            mib(sample.median),
            mib(sample.minimum),
            mib(sample.maximum),
        )?;
        peaks.insert(name.to_owned(), sample.median);
    }
    match mode {
        Mode::Measure => Ok(()),
        Mode::Save(path) => save_baseline(&path, &peaks),
        Mode::Compare(path) => compare_baseline(&path, &peaks, &mut output),
        Mode::Worker(_) => {
            Err(io::Error::new(ErrorKind::InvalidInput, "unexpected worker mode").into())
        }
    }
}

fn measure_workload(executable: &Path, path: &Path) -> io::Result<Sample> {
    let mut peaks = [0_u64; SAMPLES];
    for peak in &mut peaks {
        let result =
            Command::new(executable).arg("--worker").arg(path).output().map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!("cannot run memory worker for {}: {error}", path.display()),
                )
            })?;
        if !result.status.success() {
            return Err(io::Error::other(format!(
                "memory worker for {} failed: {}",
                path.display(),
                String::from_utf8_lossy(&result.stderr).trim()
            )));
        }
        let text = std::str::from_utf8(&result.stdout).map_err(|error| {
            io::Error::new(ErrorKind::InvalidData, format!("invalid memory worker output: {error}"))
        })?;
        *peak = text.trim().parse().map_err(|error| {
            io::Error::new(
                ErrorKind::InvalidData,
                format!("invalid peak RSS for {}: {error}", path.display()),
            )
        })?;
    }
    peaks.sort_unstable();
    Ok(Sample { median: peaks[1], minimum: peaks[0], maximum: peaks[2] })
}

fn run_worker(path: &Path) -> Result<(), Box<dyn Error>> {
    let result = analyze_files(&[path.to_path_buf()], &[], Curve::Bn254)?;
    if !result.diagnostics.is_empty() {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            format!("benchmark circuit {} has source diagnostics", path.display()),
        )
        .into());
    }
    black_box(result);
    writeln!(io::stdout().lock(), "{}", peak_rss_bytes()?)?;
    Ok(())
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn peak_rss_bytes() -> io::Result<u64> {
    let mut usage = std::mem::MaybeUninit::<libc::rusage>::uninit();
    // SAFETY: getrusage writes a complete rusage on success, and the pointer is valid.
    if unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: getrusage succeeded and initialized the value above.
    let usage = unsafe { usage.assume_init() };
    let peak = u64::try_from(usage.ru_maxrss)
        .map_err(|_| io::Error::new(ErrorKind::InvalidData, "negative peak RSS"))?;
    #[cfg(target_os = "linux")]
    let peak = peak
        .checked_mul(1024)
        .ok_or_else(|| io::Error::new(ErrorKind::InvalidData, "peak RSS overflow"))?;
    if peak == 0 {
        return Err(io::Error::new(ErrorKind::InvalidData, "zero peak RSS"));
    }
    Ok(peak)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn peak_rss_bytes() -> io::Result<u64> {
    Err(io::Error::new(ErrorKind::Unsupported, "peak RSS benchmarking supports macOS and Linux"))
}

fn save_baseline(path: &Path, peaks: &BTreeMap<String, u64>) -> Result<(), Box<dyn Error>> {
    let baseline = json!({
        "version": 1,
        "platform": format!("{}-{}", env::consts::OS, env::consts::ARCH),
        "samples_per_workload": SAMPLES,
        "peak_rss_bytes": peaks,
    });
    let mut bytes = serde_json::to_vec_pretty(&baseline)?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("cannot save memory baseline {}: {error}", path.display()),
        )
    })?;
    writeln!(io::stdout().lock(), "Saved memory baseline to {}.", path.display())?;
    Ok(())
}

fn read_baseline(path: &Path) -> Result<BTreeMap<String, u64>, Box<dyn Error>> {
    let bytes = fs::read(path).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("cannot read memory baseline {}: {error}", path.display()),
        )
    })?;
    let value: Value = serde_json::from_slice(&bytes).map_err(|error| {
        io::Error::new(
            ErrorKind::InvalidData,
            format!("invalid memory baseline {}: {error}", path.display()),
        )
    })?;
    let platform = format!("{}-{}", env::consts::OS, env::consts::ARCH);
    if value["version"].as_u64() != Some(1)
        || value["platform"].as_str() != Some(platform.as_str())
        || value["samples_per_workload"].as_u64() != Some(SAMPLES as u64)
    {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            format!("memory baseline {} has an unsupported version or platform", path.display()),
        )
        .into());
    }
    let entries = value["peak_rss_bytes"].as_object().ok_or_else(|| {
        io::Error::new(ErrorKind::InvalidData, "memory baseline has no peak_rss_bytes object")
    })?;
    let mut peaks = BTreeMap::new();
    for (name, peak) in entries {
        let bytes = peak.as_u64().filter(|bytes| *bytes > 0).ok_or_else(|| {
            io::Error::new(ErrorKind::InvalidData, format!("invalid peak RSS for {name}"))
        })?;
        peaks.insert(name.clone(), bytes);
    }
    Ok(peaks)
}

fn compare_baseline(
    path: &Path,
    current: &BTreeMap<String, u64>,
    output: &mut impl Write,
) -> Result<(), Box<dyn Error>> {
    let baseline = read_baseline(path)?;
    if baseline.keys().ne(current.keys()) {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            format!("memory baseline {} does not match the current workloads", path.display()),
        )
        .into());
    }
    let mut regressions = Vec::new();
    for (name, peak) in current {
        let before = baseline[name];
        let scaled = u128::from(*peak) * 1_000 / u128::from(before);
        let (sign, change) =
            if scaled >= 1_000 { ('+', scaled - 1_000) } else { ('-', 1_000 - scaled) };
        let exceeds =
            u128::from(*peak) * 100 > u128::from(before) * u128::from(100 + MAX_INCREASE_PERCENT);
        writeln!(output, "{name}: {sign}{}.{:01}% versus baseline", change / 10, change % 10)?;
        if exceeds {
            regressions.push(name.as_str());
        }
    }
    output.flush()?;
    if !regressions.is_empty() {
        return Err(io::Error::other(format!(
            "peak RSS increased by more than {MAX_INCREASE_PERCENT}% for: {}",
            regressions.join(", ")
        ))
        .into());
    }
    Ok(())
}

fn mib(bytes: u64) -> String {
    const MIB: u64 = 1024 * 1024;
    format!("{}.{:01}", bytes / MIB, bytes % MIB * 10 / MIB)
}
