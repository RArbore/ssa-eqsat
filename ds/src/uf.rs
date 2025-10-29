use core::cell::{Cell, RefCell};
use core::fmt::Debug;
use std::collections::BTreeSet;

pub trait Group: Clone + Debug + PartialEq + Eq {
    fn identity() -> Self;
    fn compose(&self, other: &Self) -> Self;
    fn inverse(&self) -> Self;
}

impl Group for () {
    fn identity() -> Self {
        ()
    }

    fn compose(&self, _: &Self) -> Self {
        ()
    }

    fn inverse(&self) -> Self {
        ()
    }
}

impl Group for i32 {
    fn identity() -> Self {
        0
    }

    fn compose(&self, other: &Self) -> Self {
        self + *other
    }

    fn inverse(&self) -> Self {
        -*self
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ClassId(u32);

impl From<u32> for ClassId {
    fn from(value: u32) -> Self {
        ClassId(value)
    }
}

impl From<ClassId> for u32 {
    fn from(value: ClassId) -> Self {
        value.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LabelledUnionFind<G: Group> {
    vec: RefCell<Vec<(ClassId, G)>>,
    num_classes: Cell<u32>,
}

impl<G: Group> LabelledUnionFind<G> {
    pub fn new() -> Self {
        Self {
            vec: RefCell::new(Vec::new()),
            num_classes: Cell::new(0),
        }
    }

    pub fn new_all_not_equals(amount: u32) -> Self {
        Self {
            vec: RefCell::new(
                (0..amount)
                    .map(|idx| (ClassId(idx), G::identity()))
                    .collect(),
            ),
            num_classes: Cell::new(amount),
        }
    }

    pub fn makeset(&self) -> ClassId {
        let mut vec = self.vec.borrow_mut();
        let len = vec.len();
        let id = ClassId(len.try_into().unwrap());
        vec.push((id, G::identity()));
        self.num_classes.set(self.num_classes.get() + 1);
        id
    }

    pub fn num_class_ids(&self) -> u32 {
        self.vec.borrow().len().try_into().unwrap()
    }

    pub fn num_classes(&self) -> u32 {
        self.num_classes.get()
    }

    pub fn find(&self, id: ClassId) -> (ClassId, G) {
        let (parent, action) = self.parent(id);
        if parent != id {
            let (root, root_action) = self.find(parent);
            let composed = action.compose(&root_action);
            self.set_parent(id, (root, composed.clone()));
            (root, composed)
        } else {
            (parent, action)
        }
    }

    pub fn query(&self, a: ClassId, b: ClassId) -> Option<G> {
        let (a_root, a_action) = self.find(a);
        let (b_root, b_action) = self.find(b);
        if a_root == b_root {
            Some(a_action.compose(&b_action.inverse()))
        } else {
            None
        }
    }

    #[inline]
    fn parent(&self, id: ClassId) -> (ClassId, G) {
        self.vec.borrow()[id.0 as usize].clone()
    }

    #[inline]
    fn set_parent(&self, id: ClassId, parent: (ClassId, G)) {
        self.vec.borrow_mut()[id.0 as usize] = parent;
    }

    pub fn merge(&self, a: ClassId, b: ClassId, action: G) -> ClassId {
        let (a_root, a_action) = self.find(a);
        let (b_root, b_action) = self.find(b);
        if a_root == b_root {
            let old_action = a_action.compose(&b_action.inverse());
            if old_action != action {
                panic!(
                    "Disagreeing relations in labelled UF for IDs {:?} and {:?}: {:?} != {:?}",
                    a, b, old_action, action
                );
            }
            a_root
        } else if a_root < b_root {
            self.set_parent(
                b_root,
                (
                    a_root,
                    b_action
                        .inverse()
                        .compose(&action.inverse())
                        .compose(&a_action),
                ),
            );
            self.num_classes.set(self.num_classes.get() - 1);
            a_root
        } else {
            self.set_parent(
                a_root,
                (
                    b_root,
                    a_action.inverse().compose(&action).compose(&b_action),
                ),
            );
            self.num_classes.set(self.num_classes.get() - 1);
            b_root
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptionalLabelledUnionFind<G: Group> {
    uf: LabelledUnionFind<G>,
    some_set: RefCell<BTreeSet<ClassId>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OptionalQueryResult<G: Group> {
    Related(G),
    Unrelated,
    Unknown,
}

impl<G: Group> OptionalLabelledUnionFind<G> {
    pub fn new() -> Self {
        Self {
            uf: LabelledUnionFind::new(),
            some_set: RefCell::new(BTreeSet::new()),
        }
    }

    pub fn new_all_none(amount: u32) -> Self {
        Self {
            uf: LabelledUnionFind::new_all_not_equals(amount),
            some_set: RefCell::new(BTreeSet::new()),
        }
    }

    pub fn makeset(&self) -> ClassId {
        self.uf.makeset()
    }

    pub fn num_class_ids(&self) -> u32 {
        self.uf.num_class_ids()
    }

    pub fn find(&self, id: ClassId) -> Option<(ClassId, G)> {
        if self.some_set.borrow().contains(&id) {
            Some(self.uf.find(id))
        } else {
            None
        }
    }

    pub fn witness(&self, id: ClassId) {
        if !self.some_set.borrow().contains(&id) {
            assert_eq!(self.uf.parent(id), (id, G::identity()));
        }
        self.some_set.borrow_mut().insert(id);
    }

    pub fn find_or_witness(&self, id: ClassId) -> (ClassId, G) {
        self.find(id).unwrap_or_else(|| {
            self.witness(id);
            (id, G::identity())
        })
    }

    pub fn query(&self, a: ClassId, b: ClassId) -> OptionalQueryResult<G> {
        if self.some_set.borrow().contains(&a) && self.some_set.borrow().contains(&b) {
            match self.uf.query(a, b) {
                Some(g) => OptionalQueryResult::Related(g),
                None => OptionalQueryResult::Unrelated,
            }
        } else {
            OptionalQueryResult::Unknown
        }
    }

    pub fn merge(&self, a: ClassId, b: ClassId, action: G) -> ClassId {
        self.witness(a);
        self.witness(b);
        self.uf.merge(a, b, action)
    }

    pub fn canon(&self, uf: &UnionFind) {
        let somes = self
            .some_set
            .borrow()
            .iter()
            .map(|id| *id)
            .collect::<Vec<_>>();
        for some in somes {
            if uf.find(some) != some {
                self.merge(uf.find(some), some, G::identity());
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnionFind {
    uf: LabelledUnionFind<()>,
}

impl UnionFind {
    pub fn new() -> Self {
        Self {
            uf: LabelledUnionFind::new(),
        }
    }

    pub fn new_all_not_equals(amount: u32) -> Self {
        Self {
            uf: LabelledUnionFind::new_all_not_equals(amount),
        }
    }

    pub fn makeset(&self) -> ClassId {
        self.uf.makeset()
    }

    pub fn num_class_ids(&self) -> u32 {
        self.uf.num_class_ids()
    }

    pub fn num_classes(&self) -> u32 {
        self.uf.num_classes()
    }

    pub fn find(&self, id: ClassId) -> ClassId {
        self.uf.find(id).0
    }

    pub fn merge(&self, a: ClassId, b: ClassId) -> ClassId {
        self.uf.merge(a, b, ())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_uf() {
        let uf = UnionFind::new();
        let x = uf.makeset();
        let y = uf.makeset();
        let z = uf.makeset();
        assert_ne!(x, y);
        assert_ne!(y, z);
        assert_ne!(z, x);
        assert_eq!(uf.find(x), x);
        assert_eq!(uf.find(y), y);
        assert_eq!(uf.find(z), z);
        assert_eq!(uf.num_classes(), 3);
        assert_eq!(uf.merge(x, x), x);
        assert_eq!(uf.merge(y, y), y);
        assert_eq!(uf.merge(z, z), z);
        assert_eq!(uf.num_classes(), 3);
        assert_eq!(uf.merge(x, y), x);
        assert_eq!(uf.find(x), uf.find(y));
        assert_ne!(uf.find(x), uf.find(z));
        assert_eq!(uf.num_classes(), 2);
        assert_eq!(uf.merge(y, x), x);
        assert_eq!(uf.num_classes(), 2);
        assert_eq!(uf.merge(x, z), x);
        assert_eq!(uf.find(x), uf.find(z));
        assert_eq!(uf.find(y), uf.find(z));
        assert_eq!(uf.find(y), uf.find(x));
        assert_eq!(uf.num_classes(), 1);
        assert_eq!(uf.merge(x, y), x);
        assert_eq!(uf.merge(z, y), x);
        assert_eq!(uf.num_classes(), 1);
    }

    #[test]
    fn complex_uf() {
        let uf = UnionFind::new();
        let mut ids = vec![];
        for i in 0..1000 {
            ids.push(uf.makeset());
            assert_eq!(uf.num_classes(), i + 1);
        }
        for i in 0..999 {
            assert_ne!(uf.find(ids[i]), uf.find(ids[i + 1]));
        }
        for i in 0..500 {
            assert_eq!(uf.merge(ids[2 * i], ids[2 * i + 1]), ids[2 * i]);
            assert_eq!(uf.num_classes() as usize, 999 - i);
        }
        for i in 0..500 {
            assert_eq!(uf.find(ids[2 * i]), uf.find(ids[2 * i + 1]));
            if i < 499 {
                assert_ne!(uf.find(ids[2 * i]), uf.find(ids[2 * i + 2]));
            }
        }
        for i in 0..499 {
            assert_eq!(uf.merge(ids[2 * i], ids[2 * i + 2]), ids[0]);
            assert_eq!(uf.num_classes() as usize, 499 - i);
        }
        for i in 0..999 {
            assert_eq!(uf.find(ids[i]), uf.find(ids[999]));
        }
    }
}
