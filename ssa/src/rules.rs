use core::cmp::max;
use core::mem::replace;

use ds::table::{Table, Value};
use ds::uf::{OptionalLabelledUnionFind, OptionalQueryResult};
use imp::term::{BinaryOp, BlockId, UnaryOp};

use crate::egraph::{Analyses, EGraph, cfg_canon};
use crate::lattices::Interval;

impl EGraph {
    fn rewrite1(&mut self) {
        // phi(x, x) => x
        let mut matches = vec![];
        for (phi, _) in self.phi.rows() {
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
        for (phi, _) in self.phi.rows() {
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
        for (phi, _) in self.phi.rows() {
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
        for (row, _) in self.analyses.interval.rows() {
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
        for (row, _) in self.binary.rows() {
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
        for (mul, _) in self.binary.rows() {
            if mul[0] == BinaryOp::Mul as Value {
                for (two, _) in self.constant.rows() {
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
        for (mul, _) in self.binary.rows() {
            if mul[0] == BinaryOp::Mul as Value {
                for (one, _) in self.constant.rows() {
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

    fn rewrite9(&mut self) {
        // x == x => 1
        // x != x => 0
        let mut matches = vec![];
        for (binary, _) in self.binary.rows() {
            if binary[0] == BinaryOp::EE as Value && binary[1] == binary[2] {
                matches.push((binary[3], 1));
            } else if binary[0] == BinaryOp::NE as Value && binary[1] == binary[2] {
                matches.push((binary[3], 0));
            }
        }

        let mut merge = |a: Value, b: Value| -> Value { self.uf.merge(a.into(), b.into()).into() };
        for m in matches {
            self.constant.insert(&[m.1, m.0.into()], &mut merge);
        }
    }

    fn rewrite10(&mut self) {
        // x - x => 0
        let mut matches = vec![];
        for (binary, _) in self.binary.rows() {
            if binary[0] == BinaryOp::Sub as Value && binary[1] == binary[2] {
                matches.push(binary[3]);
            }
        }

        let mut merge = |a: Value, b: Value| -> Value { self.uf.merge(a.into(), b.into()).into() };
        for m in matches {
            self.constant.insert(&[0, m.into()], &mut merge);
        }
    }

    fn rewrite11(&mut self) {
        // a * (b + c) => a * b + a * c
        let mut matches = vec![];
        for (mul, _) in self.binary.rows() {
            if mul[0] == BinaryOp::Mul as Value {
                for (add, _) in self.binary.rows() {
                    if add[0] == BinaryOp::Add as Value && add[3] == mul[1] {
                        matches.push((mul[2], add[1], add[2], mul[3]));
                    } else if add[0] == BinaryOp::Add as Value && add[3] == mul[2] {
                        matches.push((mul[1], add[1], add[2], mul[3]));
                    }
                }
            }
        }

        let mut merge = |a: Value, b: Value| -> Value { self.uf.merge(a.into(), b.into()).into() };
        for m in matches {
            let a_b = self.binary.insert(&[BinaryOp::Mul as Value, m.0, m.1, self.uf.makeset().into()], &mut merge).0[3].into();
            let a_c = self.binary.insert(&[BinaryOp::Mul as Value, m.0, m.2, self.uf.makeset().into()], &mut merge).0[3].into();
            self.binary.insert(&[BinaryOp::Add as Value, a_b, a_c, m.3], &mut merge);
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
        for (row, _) in self.constant.rows() {
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
        for (row, _) in self.param.rows() {
            let interval = self.interval_interner.intern(Interval::top()).into();
            self.analyses
                .interval
                .insert(&[row[1], interval], &mut merge);
        }
    }

    fn analysis5(&mut self) {
        // <>(x), x = [a, b] => <>([a, b])
        let mut merge = self.interval_interner.merge();
        for (row, _) in self.unary.rows() {
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
        for (row, _) in self.binary.rows() {
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
        let get_interval_on_edge =
            |interval: &Table, edge: (BlockId, BlockId), input: Value| -> (Option<Interval>, bool) {
                let is_back_edge = self.back_edges.contains(&edge);
                let Some(unreachable) = self.analyses.edge_unreachability.get(&[edge.0, edge.1])
                else {
                    return (None, false);
                };
                let unreachable = unreachable.unwrap() == 1;
                if !unreachable
                    && is_back_edge
                    && let Some(old_interval) = old_analyses.interval.get(&[input])
                {
                    (Some(self.interval_interner.get(old_interval.unwrap().into())), true)
                } else if unreachable || is_back_edge {
                    (Some(Interval::bottom()), false)
                } else if let Some(value) = interval.get(&[input]) {
                    (Some(self.interval_interner.get(value.unwrap().into())), false)
                } else {
                    (None, false)
                }
            };
        let mut merge = self.interval_interner.merge();
        for (row, _) in self.phi.rows() {
            let block = row[0];
            let lhs_pred = self.cfg[&block][0].0;
            let rhs_pred = self.cfg[&block][1].0;
            let (Some(lhs_interval), lhs_widen) =
                get_interval_on_edge(&self.analyses.interval, (lhs_pred, block), row[1])
            else {
                continue;
            };
            let (Some(rhs_interval), rhs_widen) =
                get_interval_on_edge(&self.analyses.interval, (rhs_pred, block), row[2])
            else {
                continue;
            };
            let mut combined: Value = self
                .interval_interner
                .intern(lhs_interval.union(&rhs_interval))
                .into();
            if lhs_widen || rhs_widen {
                let old = old_analyses.interval.get(&[row[3]]).unwrap().unwrap();
                combined = self
                    .interval_interner
                    .intern(
                        self.interval_interner
                            .get(old.into())
                            .widen(&self.interval_interner.get(combined.into())),
                    )
                    .into();
            }
            self.analyses.interval.insert(&[row[3], combined], &mut merge);
        }
    }

    fn analysis8(&mut self) {
        // y = x + [c, c] => y = x + c
        for (row, _) in self.binary.rows() {
            if row[0] == BinaryOp::Add as Value {
                if let Some(Some(lhs_interval)) = self.analyses.interval.get(&[row[1]])
                    && let Some(cons) = self
                        .interval_interner
                        .get(lhs_interval.into())
                        .try_constant()
                {
                    self.analyses
                        .offset
                        .merge(row[3].into(), row[2].into(), cons);
                }
                if let Some(Some(rhs_interval)) = self.analyses.interval.get(&[row[2]])
                    && let Some(cons) = self
                        .interval_interner
                        .get(rhs_interval.into())
                        .try_constant()
                {
                    self.analyses
                        .offset
                        .merge(row[3].into(), row[1].into(), cons);
                }
            } else if row[0] == BinaryOp::Sub as Value {
                if let Some(Some(rhs_interval)) = self.analyses.interval.get(&[row[2]])
                    && let Some(cons) = self
                        .interval_interner
                        .get(rhs_interval.into())
                        .try_constant()
                {
                    self.analyses
                        .offset
                        .merge(row[3].into(), row[1].into(), -cons);
                }
            }
        }
    }

    fn analysis9(&mut self) {
        // x = Cons(...) | x = Param(...) => x = x + 0
        for (row, _) in self.constant.rows() {
            self.analyses.offset.witness(row[1].into());
        }
        for (row, _) in self.param.rows() {
            self.analyses.offset.witness(row[1].into());
        }
    }

    fn analysis10(&mut self) {
        // x = <>(a), y = <>(b), a = b + 0 => x = y + 0
        for (row1, _) in self.unary.rows() {
            for (row2, _) in self.unary.rows() {
                if row1[0] == row2[0]
                    && self.analyses.offset.query(row1[1].into(), row2[1].into())
                        == OptionalQueryResult::Related(0)
                {
                    self.analyses
                        .offset
                        .merge(row1[2].into(), row2[2].into(), 0);
                }
            }
        }
    }

    fn analysis11(&mut self) {
        // x = <>(a, b), y = <>(c, d), a = c + 0, b = d + 0 => x = y + 0
        for (row1, _) in self.binary.rows() {
            for (row2, _) in self.binary.rows() {
                if row1[0] == row2[0]
                    && self.analyses.offset.query(row1[1].into(), row2[1].into())
                        == OptionalQueryResult::Related(0)
                    && self.analyses.offset.query(row1[2].into(), row2[2].into())
                        == OptionalQueryResult::Related(0)
                {
                    self.analyses
                        .offset
                        .merge(row1[3].into(), row2[3].into(), 0);
                }
            }
        }
    }

    fn analysis12(&mut self, old_analyses: &Analyses) {
        // x = phi(l, a, b), y = phi(l, c, d), a = c + cons, b = d + cons => x = y + cons
        let get_offset_on_edge = |offset: &OptionalLabelledUnionFind<i32>,
                                  edge: (BlockId, BlockId),
                                  first: Value,
                                  second: Value|
         -> Option<Option<i32>> {
            let is_back_edge = self.back_edges.contains(&edge);
            let Some(unreachable) = self.analyses.edge_unreachability.get(&[edge.0, edge.1]) else {
                return None;
            };
            let unreachable = unreachable.unwrap() == 1;
            if !unreachable
                && is_back_edge
                && let OptionalQueryResult::Related(old_offset) =
                    old_analyses.offset.query(first.into(), second.into())
            {
                Some(Some(old_offset))
            } else if unreachable
                || (is_back_edge
                    && old_analyses.offset.query(first.into(), second.into())
                        == OptionalQueryResult::Unknown)
            {
                Some(None)
            } else if let OptionalQueryResult::Related(offset) =
                offset.query(first.into(), second.into())
            {
                Some(Some(offset))
            } else {
                None
            }
        };
        for (row1, _) in self.phi.rows() {
            for (row2, _) in self.phi.rows() {
                if row1[0] == row2[0] {
                    let block = row1[0];
                    let lhs_pred = self.cfg[&block][0].0;
                    let rhs_pred = self.cfg[&block][1].0;
                    let Some(lhs_offset) = get_offset_on_edge(
                        &self.analyses.offset,
                        (lhs_pred, block),
                        row1[1],
                        row2[1],
                    ) else {
                        continue;
                    };
                    let Some(rhs_offset) = get_offset_on_edge(
                        &self.analyses.offset,
                        (rhs_pred, block),
                        row1[2],
                        row2[2],
                    ) else {
                        continue;
                    };
                    match (lhs_offset, rhs_offset) {
                        (Some(lhs_offset), Some(rhs_offset)) if lhs_offset == rhs_offset => {
                            self.analyses
                                .offset
                                .merge(row1[3].into(), row2[3].into(), lhs_offset);
                        }
                        (Some(offset), None) | (None, Some(offset)) => {
                            self.analyses
                                .offset
                                .merge(row1[3].into(), row2[3].into(), offset);
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fn analysis13(&mut self) {
        // x = [c1, c1], y = [c2, c2] => x = y + (c1 - c2)
        let mut last_cons: Option<(Value, i32)> = None;
        for (row, _) in self.analyses.interval.rows() {
            if let Some(cons) = self.interval_interner.get(row[1].into()).try_constant() {
                if let Some((last_class, last_cons)) = last_cons {
                    self.analyses
                        .offset
                        .merge(last_class.into(), row[0].into(), last_cons - cons);
                }
                last_cons = Some((row[0], cons));
            }
        }
    }

    pub fn optimistic_analysis(&mut self) {
        self.analyses = Analyses::new(self.uf.num_class_ids());
        loop {
            let old_analyses = replace(&mut self.analyses, Analyses::new(self.uf.num_class_ids()));

            loop {
                self.analysis1(&old_analyses);
                self.analysis2();
                self.analysis3();
                self.analysis4();
                self.analysis5();
                self.analysis6();
                self.analysis7(&old_analyses);
                self.analysis8();
                self.analysis9();
                self.analysis10();
                self.analysis11();
                self.analysis12(&old_analyses);
                self.analysis13();

                let changed1 = self.analyses.block_unreachability.check_changed();
                let changed2 = self.analyses.edge_unreachability.check_changed();
                let changed3 = self.analyses.interval.check_changed();
                let changed4 = self.analyses.offset.check_changed();
                if !changed1 && !changed2 && !changed3 && !changed4 {
                    break;
                }
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
        for _ in 0..3 {
            self.rewrite1();
            self.rewrite2();
            self.rewrite3();
            self.rewrite4();
            self.rewrite5();
            self.rewrite6();
            self.rewrite7();
            self.rewrite8();
            self.rewrite9();
            self.rewrite10();
            self.rewrite11();

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
        for _ in 0..3 {
            self.optimistic_analysis();
            if !self.saturate_rewrites() {
                break;
            }
        }
    }
}
