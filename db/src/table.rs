use core::hash::Hasher;
use std::collections::BTreeSet;
use std::collections::btree_set::Iter;
use std::iter::Peekable;

use hashbrown::HashTable;
use hashbrown::hash_table::Entry;
use rustc_hash::FxHasher;

pub type Value = u32;
pub type RowId = u64;
type HashCode = u64;

#[derive(Debug)]
struct TableEntry {
    hash: HashCode,
    row: RowId,
}

#[derive(Debug)]
struct Rows {
    buffer: Vec<Value>,
    num_determinant: usize,
    has_dependent: bool,
}

#[derive(Debug)]
pub struct Table {
    rows: Rows,
    table: HashTable<TableEntry>,
    deleted_rows: BTreeSet<RowId>,
    delta_marker: RowId,
}

#[derive(Debug)]
struct TableRows<'a> {
    table: &'a Table,
    row: RowId,
    deleted_iter: Peekable<Iter<'a, RowId>>,
}

fn hash(determinant: &[Value]) -> HashCode {
    let mut hasher = FxHasher::default();
    for val in determinant {
        hasher.write_u32(*val);
    }
    hasher.finish()
}

impl Rows {
    fn num_rows(&self) -> RowId {
        let num_columns = self.num_determinant + self.has_dependent as usize;
        (self.buffer.len() / num_columns) as RowId
    }

    fn get_row(&self, row: RowId) -> &[Value] {
        let num_columns = self.num_determinant + self.has_dependent as usize;
        let start = (row as usize) * num_columns;
        &self.buffer[start..start + num_columns]
    }

    fn get_row_mut(&mut self, row: RowId) -> &mut [Value] {
        let num_columns = self.num_determinant + self.has_dependent as usize;
        let start = (row as usize) * num_columns;
        &mut self.buffer[start..start + num_columns]
    }

    fn add_row(&mut self, row: &[Value]) -> RowId {
        let row_id = self.num_rows();
        self.buffer.extend(row);
        row_id
    }
}

impl Table {
    pub fn new(num_determinant: usize, has_dependent: bool) -> Self {
        Self {
            rows: Rows {
                buffer: vec![],
                num_determinant,
                has_dependent,
            },
            table: HashTable::new(),
            deleted_rows: BTreeSet::new(),
            delta_marker: 0,
        }
    }

    pub fn num_determinant(&self) -> usize {
        self.rows.num_determinant
    }

    pub fn has_dependent(&self) -> bool {
        self.rows.has_dependent
    }

    pub fn mark_delta(&mut self) {
        self.delta_marker = self.rows.num_rows();
    }

    pub fn insert<'a, 'b, 'c, M>(
        &'a mut self,
        row: &'b [Value],
        merge: &mut M,
    ) -> (&'a [Value], RowId)
    where
        M: FnMut(Value, Value) -> Value,
    {
        let num_determinant = self.num_determinant();
        let has_dependent = self.has_dependent();
        assert_eq!(row.len(), num_determinant + has_dependent as usize);
        let determinant = &row[0..num_determinant];
        let hash = hash(determinant);
        let entry = self.table.entry(
            hash,
            |te| te.hash == hash && &self.rows.get_row(te.row)[0..num_determinant] == determinant,
            |te| te.hash,
        );
        match entry {
            Entry::Occupied(occupied) => {
                let row_id = occupied.get().row;
                if has_dependent {
                    let old = self.rows.get_row(row_id)[num_determinant];
                    let new = row[num_determinant];
                    self.rows.get_row_mut(row_id)[num_determinant] = merge(old, new);
                }
                (self.rows.get_row(row_id), row_id)
            }
            Entry::Vacant(vacant) => {
                let row_id = self.rows.add_row(row);
                vacant.insert(TableEntry { hash, row: row_id });
                (self.rows.get_row(row_id), row_id)
            }
        }
    }

    pub fn get<'a, 'b>(&'a self, determinant: &'b [Value]) -> Option<Option<Value>> {
        let num_determinant = self.num_determinant();
        assert_eq!(determinant.len(), num_determinant);
        let hash = hash(determinant);
        let te = self.table.find(hash, |te| {
            te.hash == hash && &self.rows.get_row(te.row)[0..num_determinant] == determinant
        });
        if let Some(te) = te {
            if self.has_dependent() {
                Some(Some(self.rows.get_row(te.row)[num_determinant]))
            } else {
                Some(None)
            }
        } else {
            None
        }
    }

    pub fn delete(&mut self, row_id: RowId) -> &[Value] {
        let row = self.rows.get_row(row_id);
        let determinant = &row[0..self.num_determinant()];
        let hash = hash(determinant);
        let entry = self
            .table
            .entry(hash, |te| te.hash == hash && te.row == row_id, |te| te.hash);
        let Entry::Occupied(occupied) = entry else {
            panic!();
        };
        occupied.remove();
        self.deleted_rows.insert(row_id);
        row
    }

    pub fn rows(&self, delta: bool) -> impl Iterator<Item = (&[Value], RowId)> + '_ {
        TableRows {
            table: self,
            row: if delta { self.delta_marker } else { 0 },
            deleted_iter: self.deleted_rows.iter().peekable(),
        }
    }

    pub fn split_rows(&self, delta: bool) -> impl Iterator<Item = (&[Value], Value, RowId)> + '_ {
        assert!(self.has_dependent());
        self.rows(delta)
            .map(|(row, id)| (&row[0..row.len() - 1], row[row.len() - 1], id))
    }

    pub fn num_rows(&self) -> RowId {
        self.rows.num_rows() - self.deleted_rows.len() as RowId
    }

    pub fn rebuild<M, C>(&mut self, merge: &mut M, canon: &mut C) -> bool
    where
        M: FnMut(Value, Value) -> Value,
        C: FnMut(&[Value], &mut Vec<Value>) -> bool,
    {
        let num_columns = self.num_determinant() + self.has_dependent() as usize;
        let mut canonized: Vec<Value> = vec![];
        let mut to_delete: Vec<RowId> = vec![];
        let mut ever_changed = false;
        loop {
            let mut changed = false;

            for (row, row_id) in self.rows(false) {
                if canon(row, &mut canonized) {
                    changed = true;
                    to_delete.push(row_id);
                } else {
                    canonized.truncate(canonized.len() - num_columns);
                }
            }

            for row in to_delete.drain(..) {
                self.delete(row);
            }

            let num_rows = canonized.len() / num_columns;
            for idx in 0..num_rows {
                let canon_row = &canonized[idx * num_columns..(idx + 1) * num_columns];
                self.insert(canon_row, merge);
            }
            canonized.clear();

            if !changed {
                break ever_changed;
            } else {
                ever_changed = true;
            }
        }
    }
}

impl<'a> Iterator for TableRows<'a> {
    type Item = (&'a [Value], RowId);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(recent_deleted) = self.deleted_iter.peek() {
            if **recent_deleted > self.row {
                break;
            } else if **recent_deleted == self.row {
                self.row += 1;
            }
            self.deleted_iter.next();
        }

        if self.row >= self.table.rows.num_rows() {
            None
        } else {
            let row = self.row;
            self.row += 1;
            Some((self.table.rows.get_row(row), row))
        }
    }
}

#[cfg(test)]
mod tests {
    use core::cmp::min;

    use crate::uf::{ClassId, UnionFind};

    use super::*;

    #[test]
    fn simple_table() {
        let mut table = Table::new(2, true);
        let mut merge = |old, _| old;
        assert_eq!(
            table.insert(&[1, 2, 3], &mut merge),
            (&[1u32, 2, 3] as _, 0)
        );
        assert_eq!(
            table.insert(&[1, 2, 4], &mut merge),
            (&[1u32, 2, 3] as _, 0)
        );
        assert_eq!(
            table.insert(&[2, 2, 4], &mut merge),
            (&[2u32, 2, 4] as _, 1)
        );
        assert_eq!(
            vec![(&[1u32, 2, 3] as _, 0), (&[2u32, 2, 4] as _, 1)],
            table.rows(false).collect::<Vec<_>>()
        );
        assert_eq!(table.delete(1), &[2, 2, 4]);
        assert_eq!(
            table.insert(&[2, 2, 5], &mut merge),
            (&[2u32, 2, 5] as _, 2)
        );
        assert_eq!(
            vec![(&[1u32, 2, 3] as _, 0), (&[2u32, 2, 5] as _, 2)],
            table.rows(false).collect::<Vec<_>>()
        );
    }

    #[test]
    fn simple_merge() {
        let mut table = Table::new(2, true);
        table.insert(&[1, 2, 5], &mut min);
        table.insert(&[1, 2, 3], &mut min);
        table.insert(&[2, 2, 7], &mut min);
        table.insert(&[2, 2, 9], &mut min);
        table.insert(&[1, 2, 4], &mut min);
        assert_eq!(
            vec![(&[1u32, 2, 3] as _, 0), (&[2u32, 2, 7] as _, 1)],
            table.rows(false).collect::<Vec<_>>()
        );
        assert_eq!(table.rows.num_rows(), 2);
    }

    #[test]
    fn simple_rebuild() {
        let mut table = Table::new(1, true);
        let uf = UnionFind::new();
        let mut merge = |old, new| uf.merge(ClassId::from(old), ClassId::from(new)).into();
        let mut canon = |row: &[Value], dst: &mut Vec<Value>| {
            let new0 = uf.find(ClassId::from(row[0])).into();
            let new1 = uf.find(ClassId::from(row[1])).into();
            dst.push(new0);
            dst.push(new1);
            new0 != row[0] || new1 != row[1]
        };

        let id1 = uf.makeset();
        let id2 = uf.makeset();
        let id3 = uf.makeset();
        let id4 = uf.makeset();

        table.insert(&[id1.into(), id2.into()], &mut merge);
        table.insert(&[id3.into(), id4.into()], &mut merge);
        assert_eq!(
            vec![(&[0u32, 1] as _, 0), (&[2u32, 3] as _, 1)],
            table.rows(false).collect::<Vec<_>>()
        );

        uf.merge(id1, id3);
        table.rebuild(&mut merge, &mut canon);

        assert_eq!(
            vec![(&[0u32, 1] as _, 0)],
            table.rows(false).collect::<Vec<_>>()
        );
    }

    #[test]
    fn simple_delta() {
        let mut table = Table::new(2, false);
        let mut merge = |_, _| panic!();
        table.insert(&[0, 1], &mut merge);
        table.insert(&[1, 2], &mut merge);
        assert_eq!(
            vec![(&[0u32, 1] as _, 0), (&[1u32, 2] as _, 1)],
            table.rows(true).collect::<Vec<_>>()
        );
        table.mark_delta();
        table.insert(&[2, 3], &mut merge);
        assert_eq!(
            vec![(&[2u32, 3] as _, 2)],
            table.rows(true).collect::<Vec<_>>()
        );
        assert_eq!(
            vec![
                (&[0u32, 1] as _, 0),
                (&[1u32, 2] as _, 1),
                (&[2u32, 3] as _, 2)
            ],
            table.rows(false).collect::<Vec<_>>()
        );
    }
}
