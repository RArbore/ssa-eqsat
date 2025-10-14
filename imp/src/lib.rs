use lalrpop_util::lalrpop_mod;

pub mod ast;
pub mod term;

lalrpop_mod!(pub grammar);
