use std::io::{Read, Result, stdin};
use std::process::Command;

use tempfile::NamedTempFile;

use imp::ast::Interner;
use imp::grammar::ProgramParser;
use imp::term::{naive_ssa_translation, terms_to_dot};

pub fn main() -> Result<()> {
    let mut interner = Interner::new();

    let mut imp_program = String::new();
    stdin().read_to_string(&mut imp_program)?;
    let ast = ProgramParser::new()
        .parse(&mut interner, &imp_program)
        .unwrap();

    for func in &ast.funcs {
        let terms = naive_ssa_translation(func);
        let mut tmp = NamedTempFile::new().unwrap();
        terms_to_dot(&terms, &mut tmp)?;
        Command::new("xdot").arg(tmp.path()).status().unwrap();
    }

    Ok(())
}
