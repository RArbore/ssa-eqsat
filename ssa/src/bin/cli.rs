use std::io::{Read, Result, stdin};
use std::process::Command;

use tempfile::NamedTempFile;

use imp::ast::Interner;
use imp::grammar::ProgramParser;
use imp::term::{naive_ssa_translation};

use ssa::EGraph;

pub fn main() -> Result<()> {
    let mut interner = Interner::new();

    let mut imp_program = String::new();
    stdin().read_to_string(&mut imp_program)?;
    let mut location = 0;
    let ast = ProgramParser::new()
        .parse(&mut interner, &mut location, &imp_program)
        .unwrap();

    for func in &ast.funcs {
        let terms = naive_ssa_translation(func);
        let mut egraph = EGraph::from_terms(&terms);
        let mut tmp = NamedTempFile::new().unwrap();
        egraph.to_dot(&mut tmp)?;
        println!("{}", tmp.path().display());
        Command::new("xdot").arg(tmp.path()).status().unwrap();
        egraph.saturate_rewrites();
        let mut tmp = NamedTempFile::new().unwrap();
        egraph.to_dot(&mut tmp)?;
        println!("{}", tmp.path().display());
        Command::new("xdot").arg(tmp.path()).status().unwrap();
    }

    Ok(())
}
