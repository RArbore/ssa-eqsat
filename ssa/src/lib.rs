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
        for (eclass_idx, eclass) in eclasses.iter().enumerate() {
            writeln!(w, "subgraph E{} {{", eclass_idx)?;
            writeln!(w, "cluster=true;")?;
            for (enode_idx, enode) in eclass.iter().enumerate() {
                writeln!(w, "N{}_{}[label=\"{}\"];", eclass_idx, enode_idx, enode.0)?;
            }
            writeln!(w, "}}")?;
        }
        for (eclass_idx, eclass) in eclasses.into_iter().enumerate() {
            for (enode_idx, enode) in eclass.into_iter().enumerate() {
                for child_idx in enode.1 {
                    writeln!(
                        w,
                        "N{}_0 -> N{}_{} [ltail=E{}];",
                        child_idx, eclass_idx, enode_idx, child_idx
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

    fn rebuild(&mut self) {
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

    pub fn saturate(&mut self) {
        self.rewrite1();
        self.rebuild();
    }
}
