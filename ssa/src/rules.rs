use core::mem::replace;
use std::collections::BTreeSet;

use db::table::Value;
use imp::term::{BinaryOp, BlockId, UnaryOp};

use crate::egraph::{Analyses, EGraph};
use crate::lattices::Interval;

impl EGraph {
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

    fn analysis1(&mut self) {
        // z => [z, z]
        let mut matches = vec![];
        for (row, _) in self.constant.rows(false) {
            matches.push((row[1], row[0]));
        }

        let mut merge = |a: Value, b: Value| -> Value {
            self.interval_interner
                .intern(
                    self.interval_interner
                        .get(a.into())
                        .intersect(&self.interval_interner.get(b.into())),
                )
                .into()
        };
        for m in matches {
            let row = [
                m.0,
                self.interval_interner
                    .intern(Interval {
                        low: m.1 as i32,
                        high: m.1 as i32,
                    })
                    .into(),
            ];
            self.analyses.interval.insert(&row, &mut merge);
        }
    }

    fn analysis2(&mut self) {
        // param => [MIN, MAX]
        let mut matches = vec![];
        for (row, _) in self.param.rows(false) {
            matches.push(row[1]);
        }

        let mut merge = |a: Value, b: Value| -> Value {
            self.interval_interner
                .intern(
                    self.interval_interner
                        .get(a.into())
                        .intersect(&self.interval_interner.get(b.into())),
                )
                .into()
        };
        for m in matches {
            let row = [m, self.interval_interner.intern(Interval::bottom()).into()];
            self.analyses.interval.insert(&row, &mut merge);
        }
    }

    fn analysis3(&mut self, old_analyses: &Analyses) {
        // <>([a, b]) => [?, ?]
        let mut matches = vec![];
        for (unary, _) in self.unary.rows(false) {
            for (input, _) in old_analyses.interval.rows(false) {
                if input[0] == unary[1] {
                    matches.push((unary[2], unary[0], input[1]));
                }
            }
        }

        let mut merge = |a: Value, b: Value| -> Value {
            self.interval_interner
                .intern(
                    self.interval_interner
                        .get(a.into())
                        .intersect(&self.interval_interner.get(b.into())),
                )
                .into()
        };
        for m in matches {
            let op = UnaryOp::n(m.1).unwrap();
            let input = self.interval_interner.get(m.2.into());
            let row = [
                m.0,
                self.interval_interner
                    .intern(input.forward_unary(op))
                    .into(),
            ];
            self.analyses.interval.insert(&row, &mut merge);
        }
    }

    fn analysis4(&mut self, old_analyses: &Analyses) {
        // <>([a, b], [c, d]) => [?, ?]
        let mut matches = vec![];
        for (binary, _) in self.binary.rows(false) {
            for (lhs, _) in old_analyses.interval.rows(false) {
                if lhs[0] == binary[1] {
                    for (rhs, _) in old_analyses.interval.rows(false) {
                        if rhs[0] == binary[2] {
                            matches.push((binary[3], binary[0], lhs[1], rhs[1]));
                        }
                    }
                }
            }
        }

        let mut merge = |a: Value, b: Value| -> Value {
            self.interval_interner
                .intern(
                    self.interval_interner
                        .get(a.into())
                        .intersect(&self.interval_interner.get(b.into())),
                )
                .into()
        };
        for m in matches {
            let op = BinaryOp::n(m.1).unwrap();
            let lhs = self.interval_interner.get(m.2.into());
            let rhs = self.interval_interner.get(m.3.into());
            let row = [
                m.0,
                self.interval_interner
                    .intern(lhs.forward_binary(&rhs, op))
                    .into(),
            ];
            self.analyses.interval.insert(&row, &mut merge);
        }
    }

    fn analysis5(&mut self, old_analyses: &Analyses) {
        // phi(x, y), x = [a, b], y != [_, _] => [a, b]
        // phi(x, y), x != [_, _], y = [a, b] => [a, b]
        // phi(x, y), x = [a, b], y = [c, d] => [a, b] \cap [c, d]
        let mut matches = vec![];
        for (phi, _) in self.phi.rows(false) {
            let preds = &self.cfg[&phi[0]];
            let lhs_reachable = old_analyses
                .edge_reachability
                .rows(false)
                .any(|(row, _)| row[0] == preds[0].0 && row[1] == phi[0]);
            let rhs_reachable = old_analyses
                .edge_reachability
                .rows(false)
                .any(|(row, _)| row[0] == preds[1].0 && row[1] == phi[0]);

            let mut lhs = None;
            let mut rhs = None;
            for (interval, _) in old_analyses.interval.rows(false) {
                if interval[0] == phi[1] && lhs_reachable {
                    lhs = Some(interval[1]);
                }
                if interval[0] == phi[2] && rhs_reachable {
                    rhs = Some(interval[1]);
                }
            }

            match (lhs, rhs) {
                (Some(interval), None) | (None, Some(interval)) => matches.push((phi[3], interval)),
                (Some(lhs), Some(rhs)) => matches.push((
                    phi[3],
                    self.interval_interner
                        .intern(
                            self.interval_interner
                                .get(lhs.into())
                                .union(&self.interval_interner.get(rhs.into())),
                        )
                        .into(),
                )),
                _ => {}
            }
        }

        let mut merge = |a: Value, b: Value| -> Value {
            self.interval_interner
                .intern(
                    self.interval_interner
                        .get(a.into())
                        .intersect(&self.interval_interner.get(b.into())),
                )
                .into()
        };
        for m in matches {
            let row = [m.0, m.1];
            self.analyses.interval.insert(&row, &mut merge);
        }
    }

    fn analysis6(&mut self, old_analyses: &Analyses) {
        // Block reachability
        let mut merge = |_, _| panic!();
        self.analyses.block_reachability.insert(&[0], &mut merge);
        for (block, preds) in &self.cfg {
            if preds.iter().any(|(pred, _)| {
                old_analyses
                    .edge_reachability
                    .rows(false)
                    .any(|(row, _)| row[0] == *pred && row[1] == *block)
            }) {
                self.analyses
                    .block_reachability
                    .insert(&[*block], &mut merge);
            }
        }
    }

    fn analysis7(&mut self, old_analyses: &Analyses) {
        // Edge reachability
        let mut merge = |_, _| panic!();
        for (block, preds) in &self.cfg {
            for (pred, cond) in preds {
                if old_analyses
                    .block_reachability
                    .rows(false)
                    .any(|(row, _)| row[0] == *pred)
                    && old_analyses.interval.rows(false).any(|(row, _)| {
                        *cond == row[0].into()
                            && self.interval_interner.get(row[1].into())
                                != Interval { low: 0, high: 0 }
                    })
                {
                    self.analyses
                        .edge_reachability
                        .insert(&[*pred, *block], &mut merge);
                }
            }
        }
    }

    pub fn optimistic_analysis(&mut self) {
        self.analyses = Analyses::new();
        for _ in 0..92 {
            let old_analyses = replace(&mut self.analyses, Analyses::new());

            self.analysis1();
            self.analysis2();
            self.analysis3(&old_analyses);
            self.analysis4(&old_analyses);
            self.analysis5(&old_analyses);
            self.analysis6(&old_analyses);
            self.analysis7(&old_analyses);

            self.widen(&old_analyses);
        }
    }

    fn widen(&mut self, old_analyses: &Analyses) {
        let widening_points: BTreeSet<BlockId> = self
            .cfg
            .iter()
            .filter_map(|(block, preds)| {
                if preds.iter().any(|(pred, _)| {
                    pred >= block
                        && old_analyses
                            .edge_reachability
                            .rows(false)
                            .any(|(row, _)| row[0] == *pred && row[1] == *block)
                }) {
                    Some(*block)
                } else {
                    None
                }
            })
            .collect();
        let widening_eclasses: BTreeSet<Value> = self
            .phi
            .rows(false)
            .filter_map(|(row, _)| {
                if widening_points.contains(&row[0]) {
                    Some(row[3])
                } else {
                    None
                }
            })
            .collect();

        let mut widen = |this_iter: Value, last_iter: Value| -> Value {
            self.interval_interner
                .intern(
                    self.interval_interner
                        .get(last_iter.into())
                        .widen(&self.interval_interner.get(this_iter.into())),
                )
                .into()
        };
        for (row, _) in old_analyses.interval.rows(false) {
            if widening_eclasses.contains(&row[0]) {
                self.analyses.interval.insert(row, &mut widen);
            }
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

    pub fn saturate_rewrites(&mut self) {
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

            let new_num_nodes = self.constant.num_rows()
                + self.param.num_rows()
                + self.phi.num_rows()
                + self.unary.num_rows()
                + self.binary.num_rows();
            let new_num_classes = self.uf.num_classes();
            if new_num_nodes != num_nodes || new_num_classes != num_classes {
                num_nodes = new_num_nodes;
                num_classes = new_num_classes
            } else {
                break;
            }

            self.rebuild();
        }
    }
}
