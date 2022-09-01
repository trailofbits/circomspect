use program_structure::cfg::{Cfg, DefinitionType};
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};

pub struct TooManyArgumentsWarning {
    definition_name: String,
    definition_type: DefinitionType,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl TooManyArgumentsWarning {
    pub fn into_report(&self) -> Report {
        let mut report = Report::warning(
            format!(
                "`{}` takes too many parameters. This increases coupling and decreases readability.",
                self.definition_name
            ),
            ReportCode::TooManyArguments,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location.clone(),
                file_id,
                format!("This {} takes too many parameters.", self.definition_type),
            );
        }
        report
    }
}

pub struct CyclomaticComplexityWarning {
    definition_name: String,
    definition_type: DefinitionType,
}

impl CyclomaticComplexityWarning {
    pub fn into_report(&self) -> Report {
        Report::warning(
            format!(
                "The {} `{}` is too complex and would benefit from being refactored into smaller components.",
                self.definition_type,
                self.definition_name
            ),
            ReportCode::CyclomaticComplexity,
        )
    }
}

const MAX_NOF_PARAMETERS: usize = 7;
const MAX_CYCLOMATIC_COMPLEXITY: usize = 20;

pub fn run_complexity_analysis(cfg: &Cfg) -> ReportCollection {
    // Compute the cyclomatic complexity as `M = E - N + 2P` where `E` is the
    // number of edges, `N` is the number of nodes, and `P` is the number of
    // connected components (which is always 1 here).
    let mut edges = 0;
    let mut nodes = 0;
    for basic_block in cfg.iter() {
        edges += basic_block.successors().len();
        nodes += 1;
    }
    let complexity = edges - nodes + 2;

    let mut reports = ReportCollection::new();
    // Generate a report if the cyclomatic complexity is high.
    if complexity > MAX_CYCLOMATIC_COMPLEXITY {
        reports.push(CyclomaticComplexityWarning {
            definition_name: cfg.name().to_string(),
            definition_type: cfg.definition_type().clone(),
        }.into_report());
    }
    // Generate a report if the number of arguments is high.
    if cfg.parameters().len() > MAX_NOF_PARAMETERS {
        reports.push(TooManyArgumentsWarning {
            definition_name: cfg.name().to_string(),
            definition_type: cfg.definition_type().clone(),
            file_id: cfg.parameters().file_id().clone(),
            file_location: cfg.parameters().file_location().clone(),
        }.into_report());
    }
    reports
}
