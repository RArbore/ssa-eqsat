use std::io::{Read, Result, stdin};
use std::process::Command;

use tempfile::NamedTempFile;

use imp::ast::Interner;
use imp::grammar::ProgramParser;
use imp::term::naive_ssa_translation;

use ssa::egraph::EGraph;

fn xdot(egraph: &EGraph) -> Result<()> {
    let mut tmp = NamedTempFile::new().unwrap();
    egraph.to_dot(&mut tmp)?;
    Command::new("xdot").arg(tmp.path()).status().unwrap();
    Ok(())
}

pub fn main() -> Result<()> {
    let mut interner = Interner::new();

    let mut imp_program = String::new();
    stdin().read_to_string(&mut imp_program)?;
    let ast = ProgramParser::new()
        .parse(&mut interner, &imp_program)
        .unwrap();

    for func in &ast.funcs {
        let terms = naive_ssa_translation(func);
        let mut egraph = EGraph::from_ssa(&terms);

        xdot(&egraph)?;
        egraph.optimistic_analysis();
        egraph.saturate_rewrites();
        xdot(&egraph)?;
    }

    Ok(())
}
