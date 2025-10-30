use core::mem::replace;

use ds::table::Value;
use ds::uf::OptionalQueryResult;
use imp::term::{BinaryOp, UnaryOp};

use crate::egraph::{Analyses, EGraph};
use crate::lattices::Interval;

impl EGraph {
    fn rewrite1(&mut self) {
        // phi(x, x) => x
        let mut matches = vec![];
        for (phi, _) in self.phi.rows(false) {
            if phi[1] == phi[2] {
                matches.push((phi[1], phi[3]));
            }
        }

        for m in matches {
            self.uf.merge(m.0.into(), m.1.into());
        }
    }

    fn rewrite2(&mut self) {
        // x = phi(a, x) => a
        // x = phi(x, a) => a
        let mut matches = vec![];
        for (phi, _) in self.phi.rows(false) {
            let preds = &self.cfg[&phi[0]];
            let lhs_reachable = self
                .analyses
                .edge_reachability
                .rows(false)
                .any(|(row, _)| row[0] == preds[0].0 && row[1] == phi[0]);
            let rhs_reachable = self
                .analyses
                .edge_reachability
                .rows(false)
                .any(|(row, _)| row[0] == preds[1].0 && row[1] == phi[0]);

            if phi[2] == phi[3] && lhs_reachable {
                matches.push((phi[1], phi[3]));
            }
            if phi[1] == phi[3] && rhs_reachable {
                matches.push((phi[2], phi[3]));
            }
        }

        for m in matches {
            self.uf.merge(m.0.into(), m.1.into());
        }
    }

    fn rewrite3(&mut self) {
        // phi(x, unreachable) => x
        // phi(unreachable, x) => x
        let mut matches = vec![];
        for (phi, _) in self.phi.rows(false) {
            let preds = &self.cfg[&phi[0]];
            let lhs_reachable = self
                .analyses
                .edge_reachability
                .rows(false)
                .any(|(row, _)| row[0] == preds[0].0 && row[1] == phi[0]);
            let rhs_reachable = self
                .analyses
                .edge_reachability
                .rows(false)
                .any(|(row, _)| row[0] == preds[1].0 && row[1] == phi[0]);

            if lhs_reachable && !rhs_reachable {
                matches.push((phi[1], phi[3]));
            } else if !lhs_reachable && rhs_reachable {
                matches.push((phi[2], phi[3]));
            }
        }

        for m in matches {
            self.uf.merge(m.0.into(), m.1.into());
        }
    }

    fn rewrite4(&mut self) {
        // [z, z] => z
        let mut matches = vec![];
        for (row, _) in self.analyses.interval.rows(false) {
            if let Some(cons) = self.interval_interner.get(row[1].into()).try_constant() {
                matches.push((cons, row[0]));
            }
        }

        let mut merge = |a: Value, b: Value| -> Value { self.uf.merge(a.into(), b.into()).into() };
        for m in matches {
            let row = [m.0 as Value, m.1];
            self.constant.insert(&row, &mut merge);
        }
    }

    fn rewrite5(&mut self) {
        // x = y + 0 => x = y
        for id in 0..self.analyses.offset.num_class_ids() {
            if let Some((root, offset)) = self.analyses.offset.find(id.into())
                && offset == 0
            {
                self.uf.merge(id.into(), root);
            }
        }
    }

    fn rewrite6(&mut self) {
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

    fn rewrite7(&mut self) {
        // 2 * x => x + x
        let mut matches = vec![];
        for (mul, _) in self.binary.rows(false) {
            if mul[0] == BinaryOp::Mul as Value {
                for (two, _) in self.constant.rows(false) {
                    if two[0] == 2 && two[1] == mul[1] {
                        matches.push((mul[2], mul[3]));
                    }
                }
            }
        }

        let mut merge = |a: Value, b: Value| -> Value { self.uf.merge(a.into(), b.into()).into() };
        for m in matches {
            let row = [BinaryOp::Add as Value, m.0, m.0, m.1];
            self.binary.insert(&row, &mut merge);
        }
    }

    fn rewrite8(&mut self) {
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

    pub fn optimistic_analysis(&mut self) {
        self.analyses = Analyses::new(self.uf.num_class_ids());
        loop {
            let old_analyses = replace(&mut self.analyses, Analyses::new(self.uf.num_class_ids()));

            if !old_analyses.changed(&self.analyses) {
                break;
            }
        }
    }

    pub fn rebuild(&mut self) -> bool {
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
        let mut interval_merge = |a: Value, b: Value| -> Value {
            self.interval_interner
                .intern(
                    self.interval_interner
                        .get(a.into())
                        .intersect(&self.interval_interner.get(b.into())),
                )
                .into()
        };
        let mut interval_canon = |row: &[Value], dst: &mut Vec<Value>| {
            let root = self.uf.find(row[0].into()).into();
            dst.push(root);
            dst.push(row[1]);
            root != row[0]
        };

        let mut ever_changed = false;
        loop {
            let mut changed = false;
            changed = self.constant.rebuild(&mut merge, &mut zero_canon) || changed;
            changed = self.param.rebuild(&mut merge, &mut zero_canon) || changed;
            changed = self.phi.rebuild(&mut merge, &mut two_canon) || changed;
            changed = self.unary.rebuild(&mut merge, &mut one_canon) || changed;
            changed = self.binary.rebuild(&mut merge, &mut two_canon) || changed;
            changed = self
                .analyses
                .interval
                .rebuild(&mut interval_merge, &mut interval_canon)
                || changed;
            self.analyses.offset.canon(&self.uf);
            if !changed {
                break ever_changed;
            } else {
                ever_changed = true;
            }
        }
    }

    pub fn saturate_rewrites(&mut self) -> bool {
        let mut ever_changed = self.rebuild();
        let mut num_nodes = self.constant.num_rows()
            + self.param.num_rows()
            + self.phi.num_rows()
            + self.unary.num_rows()
            + self.binary.num_rows();
        let mut num_classes = self.uf.num_classes();
        loop {
            self.rewrite1();
            self.rewrite2();
            self.rewrite3();
            self.rewrite4();
            self.rewrite5();
            self.rewrite6();
            self.rewrite7();
            self.rewrite8();

            let new_num_nodes = self.constant.num_rows()
                + self.param.num_rows()
                + self.phi.num_rows()
                + self.unary.num_rows()
                + self.binary.num_rows();
            let new_num_classes = self.uf.num_classes();
            if new_num_nodes != num_nodes || new_num_classes != num_classes {
                ever_changed = true;
                num_nodes = new_num_nodes;
                num_classes = new_num_classes;
            } else {
                break;
            }

            self.rebuild();
        }
        ever_changed
    }

    pub fn outer_fixpoint(&mut self) {
        loop {
            self.optimistic_analysis();
            if !self.saturate_rewrites() {
                break;
            }
        }
    }
}
