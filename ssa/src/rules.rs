use core::cmp::{max, min};
use core::mem::replace;

use ds::table::{Table, Value};
use ds::uf::OptionalQueryResult;
use imp::term::{BinaryOp, BlockId, UnaryOp};

use crate::egraph::{Analyses, EGraph, cfg_canon};
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
            let lhs_edge = [preds[0].0, phi[0]];
            let rhs_edge = [preds[1].0, phi[0]];
            let lhs_unreachable = self.analyses.edge_unreachability.get(&lhs_edge) == Some(Some(1));
            let rhs_unreachable = self.analyses.edge_unreachability.get(&rhs_edge) == Some(Some(1));

            if phi[2] == phi[3] && !lhs_unreachable {
                matches.push((phi[1], phi[3]));
            }
            if phi[1] == phi[3] && !rhs_unreachable {
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
            let lhs_edge = [preds[0].0, phi[0]];
            let rhs_edge = [preds[1].0, phi[0]];
            let lhs_unreachable = self.analyses.edge_unreachability.get(&lhs_edge) == Some(Some(1));
            let rhs_unreachable = self.analyses.edge_unreachability.get(&rhs_edge) == Some(Some(1));

            if !lhs_unreachable && rhs_unreachable {
                matches.push((phi[1], phi[3]));
            } else if lhs_unreachable && !rhs_unreachable {
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

    fn analysis1(&mut self, old_analyses: &Analyses) {
        // Block reachability
        let mut merge = |a, b| max(a, b);
        self.analyses
            .block_unreachability
            .insert(&[0, 0], &mut merge);
        'outer: for (block, preds) in &self.cfg {
            let mut all_pred_edges_unreachable = 1;
            for (pred, _) in preds {
                if self.back_edges.contains(&(*pred, *block)) {
                    let edge_unreachable = old_analyses
                        .edge_unreachability
                        .get(&[*pred, *block])
                        .unwrap_or(Some(1))
                        .unwrap();
                    if edge_unreachable == 0 {
                        all_pred_edges_unreachable = 0;
                        break;
                    }
                } else {
                    let Some(Some(edge_unreachable)) =
                        self.analyses.edge_unreachability.get(&[*pred, *block])
                    else {
                        continue 'outer;
                    };
                    if edge_unreachable == 0 {
                        all_pred_edges_unreachable = 0;
                        break;
                    }
                }
            }
            self.analyses
                .block_unreachability
                .insert(&[*block, all_pred_edges_unreachable], &mut merge);
        }
    }

    fn analysis2(&mut self) {
        // Edge reachability
        let mut merge = |a, b| max(a, b);
        for (block, preds) in &self.cfg {
            for (pred, cond) in preds {
                let pred_unreachability = self.analyses.block_unreachability.get(&[*pred]);
                if pred_unreachability == Some(Some(1))
                    || self
                        .analyses
                        .interval
                        .get(&[(*cond).into()])
                        .map(|id| {
                            self.interval_interner.get(id.unwrap().into())
                                == Interval { low: 0, high: 0 }
                        })
                        .unwrap_or(false)
                {
                    self.analyses
                        .edge_unreachability
                        .insert(&[*pred, *block, 1], &mut merge);
                } else if pred_unreachability == Some(Some(0)) {
                    self.analyses
                        .edge_unreachability
                        .insert(&[*pred, *block, 0], &mut merge);
                }
            }
        }
    }

    fn analysis3(&mut self) {
        // Cons(c) => [c, c]
        let mut merge = self.interval_interner.merge();
        for (row, _) in self.constant.rows(false) {
            let cons = row[0] as i32;
            let interval = self
                .interval_interner
                .intern(Interval {
                    low: cons,
                    high: cons,
                })
                .into();
            self.analyses
                .interval
                .insert(&[row[1], interval], &mut merge);
        }
    }

    fn analysis4(&mut self) {
        // Param => [MIN, MAX]
        let mut merge = self.interval_interner.merge();
        for (row, _) in self.param.rows(false) {
            let interval = self.interval_interner.intern(Interval::top()).into();
            self.analyses
                .interval
                .insert(&[row[1], interval], &mut merge);
        }
    }

    fn analysis5(&mut self) {
        // <>(x), x = [a, b] => <>([a, b])
        let mut merge = self.interval_interner.merge();
        for (row, _) in self.unary.rows(false) {
            if let Some(interval) = self.analyses.interval.get(&[row[1]]) {
                let op = UnaryOp::n(row[0]).unwrap();
                let interval = self.interval_interner.get(interval.unwrap().into());
                let result = self
                    .interval_interner
                    .intern(interval.forward_unary(op))
                    .into();
                self.analyses.interval.insert(&[row[2], result], &mut merge);
            }
        }
    }

    fn analysis6(&mut self) {
        // <>(x, y), x = [a, b], y = [c, d] => <>([a, b], [c, d])
        let mut merge = self.interval_interner.merge();
        for (row, _) in self.binary.rows(false) {
            if let (Some(lhs_interval), Some(rhs_interval)) = (
                self.analyses.interval.get(&[row[1]]),
                self.analyses.interval.get(&[row[2]]),
            ) {
                let op = BinaryOp::n(row[0]).unwrap();
                let lhs_interval = self.interval_interner.get(lhs_interval.unwrap().into());
                let rhs_interval = self.interval_interner.get(rhs_interval.unwrap().into());
                let result = self
                    .interval_interner
                    .intern(lhs_interval.forward_binary(&rhs_interval, op))
                    .into();
                self.analyses.interval.insert(&[row[3], result], &mut merge);
            }
        }
    }

    fn analysis7(&mut self, old_analyses: &Analyses) {
        // phi(_, x, y), x = [a, b], y = [c, d] => [a, b] \cup [c, d]
        // phi(_, x, y), x = [a, b], y? => [a, b]
        // phi(_, x, y), x?, y = [a, b] => [a, b]
        let get_interval_on_edge = |interval: &Table,
                                    edge: (BlockId, BlockId),
                                    input: Value|
         -> Option<Interval> {
            let is_back_edge = self.back_edges.contains(&edge);
            let Some(unreachable) = self.analyses.edge_unreachability.get(&[edge.0, edge.1]) else {
                return None;
            };
            let unreachable = unreachable.unwrap() == 1;
            if unreachable || (is_back_edge && old_analyses.interval.get(&[input]).is_none()) {
                Some(Interval::bottom())
            } else if is_back_edge && let Some(old_interval) = old_analyses.interval.get(&[input]) {
                Some(self.interval_interner.get(old_interval.unwrap().into()))
            } else if let Some(value) = interval.get(&[input]) {
                Some(self.interval_interner.get(value.unwrap().into()))
            } else {
                None
            }
        };
        let mut merge = self.interval_interner.merge();
        for (row, _) in self.phi.rows(false) {
            let block = row[0];
            let lhs_pred = self.cfg[&block][0].0;
            let rhs_pred = self.cfg[&block][1].0;
            let Some(lhs_interval) =
                get_interval_on_edge(&self.analyses.interval, (lhs_pred, block), row[1])
            else {
                continue;
            };
            let Some(rhs_interval) =
                get_interval_on_edge(&self.analyses.interval, (rhs_pred, block), row[2])
            else {
                continue;
            };
            let joined = self
                .interval_interner
                .intern(lhs_interval.union(&rhs_interval))
                .into();
            self.analyses.interval.insert(&[row[3], joined], &mut merge);
        }
    }

    pub fn optimistic_analysis(&mut self) {
        self.analyses = Analyses::new(self.uf.num_class_ids());
        for _ in 0..100 {
            let old_analyses = replace(&mut self.analyses, Analyses::new(self.uf.num_class_ids()));

            for _ in 0..100 {
                self.analysis1(&old_analyses);
                self.analysis2();
                self.analysis3();
                self.analysis4();
                self.analysis5();
                self.analysis6();
                self.analysis7(&old_analyses);
            }

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
        let mut interval_merge = self.interval_interner.merge();
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
            cfg_canon(&mut self.cfg, &self.uf);
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
