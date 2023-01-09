use log::debug;
use std::path::PathBuf;
use std::collections::HashMap;

use parser::ParseResult;
use program_analysis::{
    analysis_context::{AnalysisContext, AnalysisError},
    get_analysis_passes,
};
use program_structure::{
    writers::{LogWriter, ReportWriter},
    template_data::TemplateInfo,
    function_data::FunctionInfo,
    file_definition::{FileLibrary, FileLocation, FileID},
    cfg::{Cfg, IntoCfg},
    constants::Curve,
    report::{ReportCollection, Report},
};

use crate::config;

type CfgCache = HashMap<String, Cfg>;
type ReportCache = HashMap<String, ReportCollection>;

pub struct AnalysisRunner {
    curve: Curve,
    file_library: FileLibrary,
    template_asts: TemplateInfo,
    function_asts: FunctionInfo,
    template_cfgs: CfgCache,
    function_cfgs: CfgCache,
    template_reports: ReportCache,
    function_reports: ReportCache,
}

impl AnalysisRunner {
    pub fn new(curve: &Curve) -> Self {
        AnalysisRunner {
            curve: curve.clone(),
            file_library: FileLibrary::new(),
            template_asts: TemplateInfo::new(),
            function_asts: FunctionInfo::new(),
            template_cfgs: CfgCache::new(),
            function_cfgs: CfgCache::new(),
            template_reports: ReportCache::new(),
            function_reports: ReportCache::new(),
        }
    }

    pub fn with_files(
        &mut self,
        input_files: &[PathBuf],
        writer: &mut (impl LogWriter + ReportWriter),
    ) -> &mut Self {
        let (template_asts, function_asts, file_library) =
            match parser::parse_files(input_files, &config::COMPILER_VERSION) {
                ParseResult::Program(program, warnings) => {
                    writer.write_reports(&warnings, &program.file_library);
                    (program.templates, program.functions, program.file_library)
                }
                ParseResult::Library(library, warnings) => {
                    writer.write_reports(&warnings, &library.file_library);
                    (library.templates, library.functions, library.file_library)
                }
            };
        self.template_asts = template_asts;
        self.function_asts = function_asts;
        self.file_library = file_library;

        self
    }

    pub fn file_library(&self) -> &FileLibrary {
        &self.file_library
    }

    pub fn template_names(&self) -> Vec<String> {
        // Clone template names to avoid holding multiple references to `self`.
        self.template_asts.keys().cloned().collect()
    }

    pub fn function_names(&self) -> Vec<String> {
        // Clone function names to avoid holding multiple references to `self`.
        self.function_asts.keys().cloned().collect()
    }

    fn analyze_template<W: LogWriter + ReportWriter>(&mut self, name: &str, writer: &mut W) {
        writer.write_message(&format!("analyzing template '{name}'"));

        // We take ownership of the CFG and any previously generated reports
        // here to avoid holding multiple mutable and immutable references to
        // `self`. This may lead to the CFG being regenerated during analysis if
        // the template is invoked recursively.
        let mut reports = self.take_template_reports(name);
        if let Ok(cfg) = self.take_template(name) {
            for analysis_pass in get_analysis_passes() {
                reports.append(&mut analysis_pass(self, &cfg));
            }
            // Re-insert the CFG into the hash map.
            if self.replace_template(name, cfg) {
                debug!("template `{name}` CFG was regenerated during analysis");
            }
        }
        writer.write_reports(&reports, &self.file_library);
    }

    pub fn analyze_templates<W: LogWriter + ReportWriter>(&mut self, writer: &mut W) {
        for name in self.template_names() {
            self.analyze_template(&name, writer);
        }
    }

    fn analyze_function<W: LogWriter + ReportWriter>(&mut self, name: &str, writer: &mut W) {
        writer.write_message(&format!("analyzing function '{name}'"));

        // We take ownership of the CFG and any previously generated reports
        // here to avoid holding multiple mutable and immutable references to
        // `self`. This may lead to the CFG being regenerated during analysis if
        // the function is invoked recursively.
        let mut reports = self.take_function_reports(name);
        if let Ok(cfg) = self.take_function(name) {
            for analysis_pass in get_analysis_passes() {
                reports.append(&mut analysis_pass(self, &cfg));
            }
            // Re-insert the CFG into the hash map.
            if self.replace_function(name, cfg) {
                debug!("function `{name}` CFG was regenerated during analysis");
            }
        }
        writer.write_reports(&reports, &self.file_library);
    }

    pub fn analyze_functions<W: LogWriter + ReportWriter>(&mut self, writer: &mut W) {
        for name in self.function_names() {
            self.analyze_function(&name, writer);
        }
    }

    /// Report cache from CFG generation. These will be emitted when the
    /// template is analyzed.
    fn append_template_reports(&mut self, name: &str, reports: &mut ReportCollection) {
        self.template_reports.entry(name.to_string()).or_default().append(reports);
    }

    /// Report cache from CFG generation. These will be emitted when the
    /// template is analyzed.
    fn take_template_reports(&mut self, name: &str) -> ReportCollection {
        self.template_reports.remove(name).unwrap_or_default()
    }

    /// Report cache from CFG generation. These will be emitted when the
    /// function is analyzed.
    fn append_function_reports(&mut self, name: &str, reports: &mut ReportCollection) {
        self.function_reports.entry(name.to_string()).or_default().append(reports);
    }

    /// Report cache from CFG generation. These will be emitted when the
    /// function is analyzed.
    fn take_function_reports(&mut self, name: &str) -> ReportCollection {
        self.function_reports.remove(name).unwrap_or_default()
    }

    fn cache_template(&mut self, name: &str) -> Result<&Cfg, AnalysisError> {
        if !self.template_cfgs.contains_key(name) {
            // The template CFG needs to be generated from the AST.
            if self.template_reports.get(name).is_some() {
                // We have already failed to generate the CFG.
                return Err(AnalysisError::FailedToLiftTemplate { name: name.to_string() });
            }
            // Get the AST corresponding to the template.
            let Some(ast) = self.template_asts.get(name) else {
                return Err(AnalysisError::UnknownTemplate { name: name.to_string() })
            };
            // Generate the template CFG from the AST. Cache any reports.
            let mut reports = ReportCollection::new();
            let cfg = generate_cfg(ast, &self.curve, &mut reports).map_err(|report| {
                reports.push(*report);
                AnalysisError::FailedToLiftTemplate { name: name.to_string() }
            })?;
            self.append_template_reports(name, &mut reports);
            self.template_cfgs.insert(name.to_string(), cfg);
        }
        Ok(self.template_cfgs.get(name).unwrap())
    }

    fn cache_function(&mut self, name: &str) -> Result<&Cfg, AnalysisError> {
        if !self.function_cfgs.contains_key(name) {
            // The function CFG needs to be generated from the AST.
            if self.function_reports.get(name).is_some() {
                // We have already failed to generate the CFG.
                return Err(AnalysisError::FailedToLiftFunction { name: name.to_string() });
            }
            // Get the AST corresponding to the function.
            let Some(ast) = self.function_asts.get(name) else {
                return Err(AnalysisError::UnknownFunction { name: name.to_string() })
            };
            // Generate the function CFG from the AST. Cache any reports.
            let mut reports = ReportCollection::new();
            let cfg = generate_cfg(ast, &self.curve, &mut reports).map_err(|report| {
                reports.push(*report);
                AnalysisError::FailedToLiftFunction { name: name.to_string() }
            })?;
            self.append_function_reports(name, &mut reports);
            self.function_cfgs.insert(name.to_string(), cfg);
        }
        Ok(self.function_cfgs.get(name).unwrap())
    }

    fn take_template(&mut self, name: &str) -> Result<Cfg, AnalysisError> {
        self.cache_template(name)?;
        // The CFG must be available since caching was successful.
        Ok(self.template_cfgs.remove(name).unwrap())
    }

    fn take_function(&mut self, name: &str) -> Result<Cfg, AnalysisError> {
        self.cache_function(name)?;
        // The CFG must be available since caching was successful.
        Ok(self.function_cfgs.remove(name).unwrap())
    }

    fn replace_template(&mut self, name: &str, cfg: Cfg) -> bool {
        self.template_cfgs.insert(name.to_string(), cfg).is_some()
    }

    fn replace_function(&mut self, name: &str, cfg: Cfg) -> bool {
        self.function_cfgs.insert(name.to_string(), cfg).is_some()
    }
}

impl AnalysisContext for AnalysisRunner {
    type Error = AnalysisError;

    fn is_template(&self, name: &str) -> bool {
        self.template_asts.get(name).is_some()
    }

    fn is_function(&self, name: &str) -> bool {
        self.function_asts.get(name).is_some()
    }

    fn template(&mut self, name: &str) -> Result<&Cfg, Self::Error> {
        self.cache_template(name)
    }

    fn function(&mut self, name: &str) -> Result<&Cfg, Self::Error> {
        self.cache_function(name)
    }

    fn underlying_str(
        &self,
        file_id: &FileID,
        file_location: &FileLocation,
    ) -> Result<String, Self::Error> {
        let Ok(file) = self.file_library.to_storage().get(*file_id) else {
            return Err(AnalysisError::UnknownFile { file_id: *file_id });
        };
        if file_location.end <= file.source().len() {
            Ok(file.source()[file_location.start..file_location.end].to_string())
        } else {
            Err(AnalysisError::InvalidLocation {
                file_id: *file_id,
                file_location: file_location.clone(),
            })
        }
    }
}

fn generate_cfg<Ast: IntoCfg>(
    ast: Ast,
    curve: &Curve,
    reports: &mut ReportCollection,
) -> Result<Cfg, Box<Report>> {
    ast.into_cfg(curve, reports)
        .map_err(|error| Box::new(error.into()))?
        .into_ssa()
        .map_err(|error| Box::new(error.into()))
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::{template_library::TemplateLibrary, intermediate_representation::Statement};

    use super::*;

    #[test]
    fn test_function() {
        let mut runner = runner_from_src(&[r#"
            function foo(a) {
                return a[0] + a[1];
            }
        "#]);

        // Check that `foo` is a known function, that we can access the CFG
        // for `foo`, and that the CFG is properly cached.
        assert!(runner.is_function("foo"));
        assert!(!runner.function_cfgs.contains_key("foo"));
        assert!(runner.function("foo").is_ok());
        assert!(runner.function_cfgs.contains_key("foo"));

        // Check that the `take_function` and `replace_function` APIs work as expected.
        let cfg = runner.take_function("foo").unwrap();
        assert!(!runner.function_cfgs.contains_key("foo"));
        assert!(!runner.replace_function("foo", cfg));
        assert!(runner.function_cfgs.contains_key("foo"));

        // Check that `baz` is not a known function, that attempting to access
        // `baz` produces an error, and that nothing is cached.
        assert!(!runner.is_function("baz"));
        assert!(!runner.function_cfgs.contains_key("baz"));
        assert!(matches!(runner.function("baz"), Err(AnalysisError::UnknownFunction { .. })));
        assert!(!runner.function_cfgs.contains_key("baz"));
    }

    #[test]
    fn test_template() {
        let mut runner = runner_from_src(&[r#"
            template Foo(n) {
                signal input a[2];

                a[0] === a[1];
            }
        "#]);

        // Check that `Foo` is a known template, that we can access the CFG
        // for `Foo`, and that the CFG is properly cached.
        assert!(runner.is_template("Foo"));
        assert!(!runner.template_cfgs.contains_key("Foo"));
        assert!(runner.template("Foo").is_ok());
        assert!(runner.template_cfgs.contains_key("Foo"));

        // Check that the `take_template` and `replace_template` APIs work as expected.
        let cfg = runner.take_template("Foo").unwrap();
        assert!(!runner.template_cfgs.contains_key("Foo"));
        assert!(!runner.replace_template("Foo", cfg));
        assert!(runner.template_cfgs.contains_key("Foo"));

        // Check that `Baz` is not a known template, that attempting to access
        // `Baz` produces an error, and that nothing is cached.
        assert!(!runner.is_template("Baz"));
        assert!(!runner.template_cfgs.contains_key("Baz"));
        assert!(matches!(runner.template("Baz"), Err(AnalysisError::UnknownTemplate { .. })));
        assert!(!runner.template_cfgs.contains_key("Baz"));
    }

    #[test]
    fn test_underlying_str() {
        use Statement::*;
        let mut runner = runner_from_src(&[r#"
            template Foo(n) {
                signal input a[2];

                a[0] === a[1];
            }
        "#]);

        let cfg = runner.take_template("Foo").unwrap();
        for stmt in cfg.entry_block().iter() {
            let file_id = stmt.meta().file_id().unwrap();
            let file_location = stmt.meta().file_location();
            let string = runner.underlying_str(&file_id, &file_location).unwrap();
            match stmt {
                Declaration { .. } => assert_eq!(string, "signal input a[2]"),
                ConstraintEquality { .. } => assert_eq!(string, "a[0] === a[1];"),
                _ => unreachable!(),
            }
        }
    }

    fn runner_from_src(src: &[&str]) -> AnalysisRunner {
        let mut file_content = HashMap::new();
        let mut file_library = FileLibrary::default();
        for (file_index, file_source) in src.iter().enumerate() {
            let file_name = format!("{file_index}.circom");
            let file_id = file_library.add_file(file_name, file_source.to_string());
            println!("{file_id}");
            file_content.insert(file_id, vec![parse_definition(file_source).unwrap()]);
        }
        let template_library = TemplateLibrary::new(file_content, file_library.clone());

        let mut runner = AnalysisRunner::new(&Curve::Goldilocks);
        runner.template_asts = template_library.templates;
        runner.function_asts = template_library.functions;
        runner.file_library = file_library;
        runner
    }
}
