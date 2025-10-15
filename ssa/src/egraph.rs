use std::io::{Result, Write};

use db::table::{Table, Value};
use db::uf::UnionFind;
use imp::term::{BinaryOp, Term, SSA, UnaryOp};

use crate::lattices::{Interner, Interval};

pub(crate) struct Analyses {
    pub(crate) interval: Table,
}

pub struct EGraph {
    pub(crate) constant: Table,
    pub(crate) param: Table,
    pub(crate) phi: Table,
    pub(crate) unary: Table,
    pub(crate) binary: Table,

    pub(crate) analyses: Analyses,

    pub(crate) uf: UnionFind,

    pub(crate) interval_interner: Interner<Interval>,
}

impl Analyses {
    pub(crate) fn new() -> Self {
        Analyses {
            interval: Table::new(1, true),
        }
    }
}

impl EGraph {
    pub fn from_terms(ssa: &SSA) -> EGraph {
        let mut egraph = EGraph {
            constant: Table::new(1, true),
            param: Table::new(1, true),
            phi: Table::new(3, true),
            unary: Table::new(2, true),
            binary: Table::new(3, true),
            analyses: Analyses::new(),
            uf: UnionFind::new_all_not_equals(ssa.terms().count() as u32),
            interval_interner: Interner::new(),
        };
        let mut merge =
            |a: Value, b: Value| -> Value { egraph.uf.merge(a.into(), b.into()).into() };
        for (term_id, term) in ssa.terms() {
            match term {
                Term::Constant(val) => {
                    egraph.constant.insert(&[val as Value, term_id], &mut merge);
                }
                Term::Param(idx) => {
                    egraph.param.insert(&[idx as Value, term_id], &mut merge);
                }
                Term::Phi(loc, lhs, rhs) => {
                    egraph
                        .phi
                        .insert(&[loc as Value, lhs.into(), rhs.into(), term_id], &mut merge);
                }
                Term::Unary(op, input) => {
                    egraph
                        .unary
                        .insert(&[op as Value, input.into(), term_id], &mut merge);
                }
                Term::Binary(op, lhs, rhs) => {
                    egraph
                        .binary
                        .insert(&[op as Value, lhs.into(), rhs.into(), term_id], &mut merge);
                }
            }
        }
        egraph
    }

    pub fn to_dot<W: Write>(&self, w: &mut W) -> Result<()> {
        let mut eclasses: Vec<(Vec<(String, Vec<Value>)>, Option<Interval>)> =
            vec![(vec![], None); self.uf.num_class_ids() as usize];

        for (row, _) in self.constant.rows(false) {
            eclasses[row[1] as usize].0.push((format!("{}", row[0 as usize]), vec![]));
        }
        for (row, _) in self.param.rows(false) {
            eclasses[row[1] as usize].0.push((format!("#{}", row[0 as usize]), vec![]));
        }
        for (row, _) in self.phi.rows(false) {
            eclasses[row[3] as usize].0.push((format!("Φ"), vec![row[1], row[2]]));
        }
        for (row, _) in self.unary.rows(false) {
            eclasses[row[2] as usize]
                .0.push((format!("{:?}", UnaryOp::n(row[0]).unwrap()), vec![row[1]]));
        }
        for (row, _) in self.binary.rows(false) {
            eclasses[row[3] as usize].0.push((
                format!("{:?}", BinaryOp::n(row[0]).unwrap()),
                vec![row[1], row[2]],
            ));
        }

        for (row, _) in self.analyses.interval.rows(false) {
            eclasses[row[0] as usize].1 = Some(self.interval_interner.get(row[1].into()));
        }

        writeln!(w, "digraph EGraph {{")?;
        writeln!(w, "compound=true;")?;
        writeln!(w, "rank=same;")?;
        writeln!(w, "outputorder=edgesfirst;")?;
        for (eclass_idx, eclass) in eclasses.iter().enumerate() {
            writeln!(w, "subgraph E{}_outer {{", eclass_idx)?;
            writeln!(w, "subgraph E{} {{", eclass_idx)?;
            writeln!(w, "subgraph {{")?;
            for (enode_idx, enode) in eclass.0.iter().enumerate() {
                writeln!(w, "N{}_{}[label=\"{}\"];", eclass_idx, enode_idx, enode.0)?;
            }
            writeln!(w, "}}")?;
            if let Some(interval) = eclass.1 {
                writeln!(w, "label=\"[{}, {}]\";", interval.low, interval.high)?;
            }
            writeln!(w, "cluster=true;")?;
            writeln!(w, "}}")?;
            writeln!(w, "style=invis;")?;
            writeln!(w, "cluster=true;")?;
            writeln!(w, "}}")?;
        }
        for (eclass_idx, eclass) in eclasses.into_iter().enumerate() {
            for (enode_idx, enode) in eclass.0.into_iter().enumerate() {
                for child_eclass in enode.1 {
                    writeln!(
                        w,
                        "N{}_0:s -> N{}_{} [ltail=E{}];",
                        child_eclass, eclass_idx, enode_idx, child_eclass
                    )?;
                }
            }
        }
        writeln!(w, "}}")
    }
}
