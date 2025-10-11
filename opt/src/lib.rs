use core::fmt::Write;
use std::collections::BTreeSet;

use egglog::EGraph;

use imp::term::{Term, Terms};

const DATATYPES: &'static str = r#"
(datatype Term
  (Ignore i64)
  (Cons i64)
  (Param i64)
  (Phi i64 Term Term)

  (Negate Term)
  (Not Term)

  (Add Term Term)
  (Sub Term Term)
  (Mul Term Term)
  (Div Term Term)
  (Rem Term Term)
  (EE Term Term)
  (NE Term Term)
  (LT Term Term)
  (LE Term Term)
  (GT Term Term)
  (GE Term Term)
)
"#;

const ANALYSES: &'static str = r#"
"#;

pub fn embed_terms(terms: &Terms) -> EGraph {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, DATATYPES).unwrap();

    let mut made_ignore = BTreeSet::new();
    for (id, term) in terms.terms() {
        let program = match term {
            Term::Constant(val) => format!("(let e{} (Cons {}))\n", id, val),
            Term::Param(idx) => format!("(let e{} (Param {}))\n", id, idx),
            Term::Phi(loc, lhs, rhs) => {
                let mut program = "".to_string();
                if lhs >= id && !made_ignore.contains(&lhs) {
                    made_ignore.insert(lhs);
                    write!(program, "(let e{} (Ignore {}))\n", lhs, lhs).unwrap();
                }
                if rhs >= id && !made_ignore.contains(&rhs) {
                    made_ignore.insert(rhs);
                    write!(program, "(let e{} (Ignore {}))\n", rhs, rhs).unwrap();
                }
                if made_ignore.contains(&id) {
                    write!(program, "(union e{} (Phi {} e{} e{}))\n", id, loc, lhs, rhs).unwrap();
                } else {
                    write!(program, "(let e{} (Phi {} e{} e{}))\n", id, loc, lhs, rhs).unwrap();
                }
                program
            }
            Term::Unary(op, input) => {
                let mut program = "".to_string();
                if input >= id && !made_ignore.contains(&input) {
                    made_ignore.insert(input);
                    write!(program, "(let e{} (Ignore {}))\n", input, input).unwrap();
                }
                if made_ignore.contains(&id) {
                    write!(program, "(union e{} ({:?} e{}))\n", id, op, input).unwrap();
                } else {
                    write!(program, "(let e{} ({:?} e{}))\n", id, op, input).unwrap();
                }
                program
            }
            Term::Binary(op, lhs, rhs) => {
                let mut program = "".to_string();
                if lhs >= id && !made_ignore.contains(&lhs) {
                    made_ignore.insert(lhs);
                    write!(program, "(let e{} (Ignore {}))\n", lhs, lhs).unwrap();
                }
                if rhs >= id && !made_ignore.contains(&rhs) {
                    made_ignore.insert(rhs);
                    write!(program, "(let e{} (Ignore {}))\n", rhs, rhs).unwrap();
                }
                if made_ignore.contains(&id) {
                    write!(program, "(union e{} ({:?} e{} e{}))\n", id, op, lhs, rhs).unwrap();
                } else {
                    write!(program, "(let e{} ({:?} e{} e{}))\n", id, op, lhs, rhs).unwrap();
                }
                program
            }
        };
        egraph.parse_and_run_program(None, &program).unwrap();
    }

    egraph
}
