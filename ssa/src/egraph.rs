use std::collections::BTreeSet;
use std::io::{Result, Write};
use std::process::{Command, Stdio};

use tempfile::NamedTempFile;

use ds::table::{Table, Value};
use ds::uf::{ClassId, OptionalLabelledUnionFind, UnionFind};
use imp::term::{BinaryOp, BlockId, SSA, Term, UnaryOp};

use crate::cfg::{CFG, back_edges, rpo};
use crate::lattices::{Interner, Interval};

#[derive(Debug)]
pub(crate) struct Analyses {
    pub(crate) block_unreachability: Table,
    pub(crate) edge_unreachability: Table,
    pub(crate) interval: Table,
    pub(crate) offset: OptionalLabelledUnionFind<i32>,
}

#[derive(Debug)]
pub struct EGraph {
    pub(crate) constant: Table,
    pub(crate) param: Table,
    pub(crate) phi: Table,
    pub(crate) unary: Table,
    pub(crate) binary: Table,

    pub(crate) analyses: Analyses,

    pub(crate) uf: UnionFind,
    pub(crate) interval_interner: Interner<Interval>,

    pub(crate) cfg: CFG,
    pub(crate) back_edges: BTreeSet<(BlockId, BlockId)>,
}

impl Analyses {
    pub(crate) fn new(num_classes: u32) -> Self {
        Analyses {
            block_unreachability: Table::new(1, true),
            edge_unreachability: Table::new(2, true),
            interval: Table::new(1, true),
            offset: OptionalLabelledUnionFind::new_all_none(num_classes),
        }
    }

    pub(crate) fn changed(&self, other: &Self) -> bool {
        let changed_table_map = |old: &Table, new: &Table| {
            for (row, dep, _) in new.split_rows() {
                if old.get(row) != Some(Some(dep)) {
                    return true;
                }
            }
            false
        };
        changed_table_map(&self.block_unreachability, &other.block_unreachability)
            || changed_table_map(&self.edge_unreachability, &other.edge_unreachability)
            || changed_table_map(&self.interval, &other.interval)
            || self.offset != other.offset
    }
}

impl EGraph {
    pub fn from_ssa(ssa: &SSA) -> EGraph {
        let num_classes = ssa.terms().count() as u32;
        let cfg = ssa
            .cfg
            .iter()
            .map(|(block, preds)| {
                (
                    *block,
                    preds
                        .iter()
                        .map(|(block, term)| (*block, ClassId::from(*term)))
                        .collect(),
                )
            })
            .collect();

        let back_edges = back_edges(&rpo(&cfg), &cfg);
        let mut egraph = EGraph {
            constant: Table::new(1, true),
            param: Table::new(1, true),
            phi: Table::new(3, true),
            unary: Table::new(2, true),
            binary: Table::new(3, true),
            analyses: Analyses::new(num_classes),
            uf: UnionFind::new_all_not_equals(num_classes),
            interval_interner: Interner::new(),
            cfg,
            back_edges,
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
        let mut eclasses: Vec<(Vec<(String, Vec<(Value, String)>)>, Option<Interval>)> =
            vec![(vec![], None); self.uf.num_class_ids() as usize];

        for (row, _) in self.constant.rows() {
            eclasses[row[1] as usize]
                .0
                .push((format!("{}", row[0 as usize] as i32), vec![]));
        }
        for (row, _) in self.param.rows() {
            eclasses[row[1] as usize]
                .0
                .push((format!("#{}", row[0 as usize]), vec![]));
        }
        for (row, _) in self.phi.rows() {
            let preds = &self.cfg[&row[0]];
            let lhs_unreachable = self
                .analyses
                .edge_unreachability
                .rows()
                .any(|(reach_row, _)| {
                    reach_row[0] == preds[0].0 && reach_row[1] == row[0] && reach_row[2] == 1
                });
            let rhs_unreachable = self
                .analyses
                .edge_unreachability
                .rows()
                .any(|(reach_row, _)| {
                    reach_row[0] == preds[1].0 && reach_row[1] == row[0] && reach_row[2] == 1
                });
            let lhs_back_edge = self.back_edges.contains(&(preds[0].0, row[0]));
            let rhs_back_edge = self.back_edges.contains(&(preds[1].0, row[0]));
            eclasses[row[3] as usize].0.push((
                format!("Φ"),
                vec![
                    (
                        row[1],
                        format!(
                            "style=\"{}\", color=\"{}\"",
                            if lhs_unreachable { "dashed" } else { "solid" },
                            if lhs_back_edge { "red" } else { "black" }
                        ),
                    ),
                    (
                        row[2],
                        format!(
                            "style=\"{}\", color=\"{}\"",
                            if rhs_unreachable { "dashed" } else { "solid" },
                            if rhs_back_edge { "red" } else { "black" }
                        ),
                    ),
                ],
            ));
        }
        for (row, _) in self.unary.rows() {
            eclasses[row[2] as usize].0.push((
                format!("{:?}", UnaryOp::n(row[0]).unwrap()),
                vec![(row[1], "".into())],
            ));
        }
        for (row, _) in self.binary.rows() {
            eclasses[row[3] as usize].0.push((
                format!("{:?}", BinaryOp::n(row[0]).unwrap()),
                vec![(row[1], "".into()), (row[2], "".into())],
            ));
        }

        for (row, _) in self.analyses.interval.rows() {
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
                writeln!(
                    w,
                    "label=\"{}: [{}, {}]\";",
                    eclass_idx, interval.low, interval.high
                )?;
            } else {
                writeln!(w, "label=\"{}\";", eclass_idx)?;
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
                        "N{}_0:s -> N{}_{} [ltail=E{}, {}];",
                        child_eclass.0, eclass_idx, enode_idx, child_eclass.0, child_eclass.1
                    )?;
                }
            }
        }
        writeln!(w, "}}")
    }

    pub fn xdot(&self) -> Result<()> {
        let mut tmp = NamedTempFile::new().unwrap();
        self.to_dot(&mut tmp)?;
        Command::new("xdot")
            .arg(tmp.path())
            .stderr(Stdio::null())
            .status()
            .unwrap();
        Ok(())
    }
}
