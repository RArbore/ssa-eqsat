use core::mem::swap;
use std::collections::HashSet;
use std::io::{Result, Write};

use db::table::{Table, Value};
use db::uf::UnionFind;
use imp::term::{BinaryOp, Term, Terms, UnaryOp};

pub struct EGraph {
    constant: Table,
    param: Table,
    phi: Table,
    unary: Table,
    binary: Table,
    uf: UnionFind,
}

impl EGraph {
    pub fn from_terms(terms: &Terms) -> EGraph {
        let mut egraph = EGraph {
            constant: Table::new(1, true),
            param: Table::new(1, true),
            phi: Table::new(3, true),
            unary: Table::new(2, true),
            binary: Table::new(3, true),
            uf: UnionFind::new_all_not_equals(terms.terms().count() as u32),
        };
        let mut merge =
            |a: Value, b: Value| -> Value { egraph.uf.merge(a.into(), b.into()).into() };
        for (term_id, term) in terms.terms() {
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
        let mut eclasses: Vec<Vec<(String, Vec<Value>)>> =
            vec![vec![]; self.uf.num_class_ids() as usize];
        for (row, _) in self.constant.rows(false) {
            eclasses[row[1] as usize].push((format!("{}", row[0 as usize]), vec![]));
        }
        for (row, _) in self.param.rows(false) {
            eclasses[row[1] as usize].push((format!("#{}", row[0 as usize]), vec![]));
        }
        for (row, _) in self.phi.rows(false) {
            eclasses[row[3] as usize].push((format!("Φ"), vec![row[1], row[2]]));
        }
        for (row, _) in self.unary.rows(false) {
            eclasses[row[2] as usize]
                .push((format!("{:?}", UnaryOp::n(row[0]).unwrap()), vec![row[1]]));
        }
        for (row, _) in self.binary.rows(false) {
            eclasses[row[3] as usize].push((
                format!("{:?}", BinaryOp::n(row[0]).unwrap()),
                vec![row[1], row[2]],
            ));
        }

        writeln!(w, "digraph EGraph {{")?;
        writeln!(w, "compound=true;")?;
        writeln!(w, "rank=same;")?;
        writeln!(w, "outputorder=edgesfirst;")?;
        for (eclass_idx, eclass) in eclasses.iter().enumerate() {
            writeln!(w, "subgraph E{}_outer {{", eclass_idx)?;
            writeln!(w, "subgraph E{} {{", eclass_idx)?;
            writeln!(w, "subgraph {{")?;
            for (enode_idx, enode) in eclass.iter().enumerate() {
                writeln!(w, "N{}_{}[label=\"{}\"];", eclass_idx, enode_idx, enode.0)?;
            }
            writeln!(w, "}}")?;
            writeln!(w, "label={};", eclass_idx)?;
            writeln!(w, "cluster=true;")?;
            writeln!(w, "}}")?;
            writeln!(w, "style=invis;")?;
            writeln!(w, "cluster=true;")?;
            writeln!(w, "}}")?;
        }
        for (eclass_idx, eclass) in eclasses.into_iter().enumerate() {
            for (enode_idx, enode) in eclass.into_iter().enumerate() {
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

    fn rewrite1(&mut self) {
        // x + x => 2 * x
        let mut matches = vec![];
        for (row, _) in self.binary.rows(false) {
            if row[0] == BinaryOp::Add as Value && row[1] == row[2] {
                matches.push((row[1], row[3]))
            }
        }

        let mut merge = |a: Value, b: Value| -> Value { self.uf.merge(a.into(), b.into()).into() };
        let two = self
            .constant
            .insert(&[2, self.uf.makeset().into()], &mut merge)
            .0[1]
            .into();
        for m in matches {
            let row = [BinaryOp::Mul as Value, two, m.0, m.1];
            self.binary.insert(&row, &mut merge);
        }
    }

    fn rewrite2(&mut self) {
        // 1 * x => x
        let mut matches = vec![];
        for (mul, _) in self.binary.rows(false) {
            if mul[0] == BinaryOp::Mul as Value {
                for (one, _) in self.constant.rows(false) {
                    if one[0] == 1 && one[1] == mul[1] {
                        matches.push((mul[2], mul[3]));
                    }
                }
            }
        }

        for m in matches {
            self.uf.merge(m.0.into(), m.1.into());
        }
    }

    fn rewrite3(&mut self) {
        // (x + 1) - 1 => x
        let mut matches = vec![];
        for (sub, _) in self.binary.rows(false) {
            if sub[0] == BinaryOp::Sub as Value {
                for (one, _) in self.constant.rows(false) {
                    if one[0] == 1 && one[1] == sub[2] {
                        for (add, _) in self.binary.rows(false) {
                            if add[0] == BinaryOp::Add as Value {
                                if add[3] == sub[1] && one[1] == add[2] {
                                    matches.push((add[1], sub[3]));
                                }
                            }
                        }
                    }
                }
            }
        }

        for m in matches {
            self.uf.merge(m.0.into(), m.1.into());
        }
    }

    pub fn rebuild(&mut self) {
        let mut merge = |a: Value, b: Value| -> Value { self.uf.merge(a.into(), b.into()).into() };
        let mut zero_canon = |row: &[Value], dst: &mut Vec<Value>| {
            let root = self.uf.find(row[1].into()).into();
            dst.push(row[0]);
            dst.push(root);
            root != row[1]
        };
        let mut one_canon = |row: &[Value], dst: &mut Vec<Value>| {
            let input = self.uf.find(row[1].into()).into();
            let root = self.uf.find(row[2].into()).into();
            dst.push(row[0]);
            dst.push(input);
            dst.push(root);
            input != row[1] || root != row[2]
        };
        let mut two_canon = |row: &[Value], dst: &mut Vec<Value>| {
            let lhs = self.uf.find(row[1].into()).into();
            let rhs = self.uf.find(row[2].into()).into();
            let root = self.uf.find(row[3].into()).into();
            dst.push(row[0]);
            dst.push(lhs);
            dst.push(rhs);
            dst.push(root);
            lhs != row[1] || rhs != row[2] || root != row[3]
        };
        loop {
            let mut changed = false;
            changed = self.constant.rebuild(&mut merge, &mut zero_canon) || changed;
            changed = self.param.rebuild(&mut merge, &mut zero_canon) || changed;
            changed = self.phi.rebuild(&mut merge, &mut two_canon) || changed;
            changed = self.unary.rebuild(&mut merge, &mut one_canon) || changed;
            changed = self.binary.rebuild(&mut merge, &mut two_canon) || changed;
            if !changed {
                break;
            }
        }
    }

    pub fn corebuild(&mut self) {
        let num_class_ids = self.uf.num_class_ids();
        let mut last_uf = UnionFind::new_all_equals(num_class_ids);
        let mut next_uf = UnionFind::new_all_not_equals(num_class_ids);

        let mut constant_obs = vec![HashSet::<[Value; 2]>::new(); num_class_ids as usize];
        let mut param_obs = vec![HashSet::<[Value; 2]>::new(); num_class_ids as usize];
        let mut phi_obs = vec![HashSet::<[Value; 4]>::new(); num_class_ids as usize];
        let mut unary_obs = vec![HashSet::<[Value; 3]>::new(); num_class_ids as usize];
        let mut binary_obs = vec![HashSet::<[Value; 4]>::new(); num_class_ids as usize];

        loop {
            let zero_canonicalize = |row: &[Value]| [row[0], last_uf.find(row[1].into()).into()];
            let one_canonicalize = |row: &[Value]| {
                [
                    row[0],
                    last_uf.find(row[1].into()).into(),
                    last_uf.find(row[2].into()).into(),
                ]
            };
            let two_canonicalize = |row: &[Value]| {
                [
                    row[0],
                    last_uf.find(row[1].into()).into(),
                    last_uf.find(row[2].into()).into(),
                    last_uf.find(row[3].into()).into(),
                ]
            };

            for (row, _) in self.constant.rows(false) {
                constant_obs[row[1] as usize].insert(zero_canonicalize(row));
            }
            for (row, _) in self.param.rows(false) {
                param_obs[row[1] as usize].insert(zero_canonicalize(row));
            }
            for (row, _) in self.phi.rows(false) {
                phi_obs[row[3] as usize].insert(two_canonicalize(row));
            }
            for (row, _) in self.unary.rows(false) {
                unary_obs[row[2] as usize].insert(one_canonicalize(row));
            }
            for (row, _) in self.binary.rows(false) {
                binary_obs[row[3] as usize].insert(two_canonicalize(row));
            }

            for lhs in 0..num_class_ids {
                for rhs in 0..num_class_ids {
                    if !constant_obs[lhs as usize].is_disjoint(&constant_obs[rhs as usize])
                        || !param_obs[lhs as usize].is_disjoint(&param_obs[rhs as usize])
                        || !phi_obs[lhs as usize].is_disjoint(&phi_obs[rhs as usize])
                        || !unary_obs[lhs as usize].is_disjoint(&unary_obs[rhs as usize])
                        || !binary_obs[lhs as usize].is_disjoint(&binary_obs[rhs as usize])
                    {
                        next_uf.merge(lhs.into(), rhs.into());
                    }
                }
            }

            if last_uf == next_uf {
                break;
            } else {
                swap(&mut last_uf, &mut next_uf);
                next_uf.set_all_not_equals();
                constant_obs.clear();
                constant_obs.resize(num_class_ids as usize, HashSet::new());
                param_obs.clear();
                param_obs.resize(num_class_ids as usize, HashSet::new());
                phi_obs.clear();
                phi_obs.resize(num_class_ids as usize, HashSet::new());
                unary_obs.clear();
                unary_obs.resize(num_class_ids as usize, HashSet::new());
                binary_obs.clear();
                binary_obs.resize(num_class_ids as usize, HashSet::new());
            }
        }

        for idx in 0..num_class_ids {
            self.uf.merge(idx.into(), last_uf.find(idx.into()));
        }
    }

    pub fn saturate(&mut self) {
        self.rewrite1();
        self.rewrite2();
        self.rewrite3();
        self.rebuild();
    }
}
