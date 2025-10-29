use std::io::{Read, Result, stdin};

use imp::ast::Interner;
use imp::grammar::ProgramParser;
use imp::term::naive_ssa_translation;

use ssa::egraph::EGraph;

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

        egraph.optimistic_analysis();
        egraph.xdot()?;
        egraph.saturate_rewrites();
        egraph.xdot()?;
        egraph.optimistic_analysis();
        egraph.xdot()?;
    }

    Ok(())
}
