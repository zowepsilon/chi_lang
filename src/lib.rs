use std::{io, fs};
use std::path::{Path, PathBuf};
use std::process::Command;

use analysis::{AnalysisError, ModuleScope, resources::PACKAGES};
use compilation::CompilationError;
use parser::ParserError;

pub mod analysis;
pub mod ast;
pub mod compilation;
pub mod lexer;
pub mod parser;
pub mod transpiler;

#[derive(Debug)]
pub enum TranspileError {
    FileNameError(String),
    FileError(io::Error),
    WrongExtension(PathBuf),
    NonAlphanumericModuleName(String),
    ParserError(Vec<ParserError>),
    AnalysisError(AnalysisError),
}

fn transpile(main_file: &str, target_dir: &str) -> Result<String, TranspileError> {
    fs::create_dir_all(target_dir).map_err(|e| TranspileError::FileError(e))?;

    let main_path = Path::new(main_file).to_path_buf();

    let module_name = ModuleScope::main(main_path)?;

    let mut transpiled_file = PathBuf::from(target_dir);
    transpiled_file.push(format!("{module_name}.c"));

    PACKAGES.with(|p| p.get_mut(&module_name).expect("ModuleScope::main adds module to PACKAGES").analyse()).map_err(|e| TranspileError::AnalysisError(e))?;

    PACKAGES.with(|p| p.get_mut(&module_name).expect("ModuleScope::main adds module to PACKAGES").transpile(transpiled_file))?;

    Ok(module_name)
}

fn compile(main_file: &str, target_dir: &str) -> Result<String, CompilationError> {

    let module_name =
        transpile(main_file, target_dir).map_err(|e| CompilationError::TranspileError(e))?;

    let mut transpiled_file = PathBuf::from(target_dir);
    let mut log_file = PathBuf::from(target_dir);
    let mut binary_file = PathBuf::from(target_dir);

    transpiled_file.push(format!("{module_name}.c"));
    log_file.push("chi_compiler.log");
    binary_file.push(format!("{module_name}"));

    compilation::compile(transpiled_file, log_file, binary_file)?;
    Ok(module_name)
}

pub fn compile_and_run(main_file: &str, target_dir: &str) -> Result<u8, CompilationError> {
    let module_name = compile(main_file, target_dir)?;

    let mut binary_file = PathBuf::from(target_dir);
    binary_file.push(format!("{module_name}"));

    Ok(Command::new(format!("{}", binary_file.display()))
        .status()
        .unwrap()
        .code()
        .unwrap_or(-1) as u8)
}

#[cfg(test)]
mod tests {
    pub fn compile_and_test(
        main_file: &'static str,
        target_dir: &str,
    ) -> Result<u8, super::CompilationError> {
        use std::{fs, process, path::PathBuf};

        // clear the previously generated code
        let _ = fs::remove_dir_all(target_dir);

        let module_name = super::compile(main_file, target_dir)?;

        let mut binary_file = PathBuf::from(target_dir);
        binary_file.push(format!("{module_name}"));    

        Ok(
            process::Command::new(format!("{}", binary_file.display()))
                // don't print program output during tests!
                .stdout(process::Stdio::null())
                .stderr(process::Stdio::null())
                .status()
                .unwrap()
                .code()
                .unwrap_or(-1) as u8,
        )
    }

    macro_rules! test_program {
        ($name:ident: $path:expr) => {
            #[test]
            fn $name() {
                let result =                       // tests are multithreaded so we need a seperate `generated/` folder for each test
                    compile_and_test($path, &format!("generated_tests/{}", stringify!($name)))
                        .unwrap();
                assert_eq!(result, 0);
            }
        };
    }

    test_program!(test_assignment: "examples/assignment.chi");
    test_program!(test_control_flow: "examples/control_flow.chi");
    test_program!(test_externs: "examples/externs.chi");
    test_program!(test_literals: "examples/literals.chi");
    test_program!(test_newlines: "examples/newlines.chi");
    test_program!(test_recursion: "examples/recursion.chi");
    test_program!(test_references: "examples/references.chi");
    test_program!(test_shadowing: "examples/shadowing.chi");
    test_program!(test_structs: "examples/structs.chi");
    test_program!(test_modules: "examples/modules/modules.chi");
    test_program!(test_helloworld: "examples/helloworld.chi");
    test_program!(test_methods: "examples/methods.chi");
}
