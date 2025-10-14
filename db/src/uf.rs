use core::cell::{Cell, RefCell};

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
pub struct UnionFind {
    vec: RefCell<Vec<ClassId>>,
    num_classes: Cell<u32>,
}

impl UnionFind {
    pub fn new() -> Self {
        Self {
            vec: RefCell::new(Vec::new()),
            num_classes: Cell::new(0),
        }
    }

    pub fn new_all_not_equals(amount: u32) -> Self {
        Self {
            vec: RefCell::new((0..amount).map(|idx| ClassId(idx)).collect()),
            num_classes: Cell::new(amount),
        }
    }

    pub fn new_all_equals(amount: u32) -> Self {
        Self {
            vec: RefCell::new(vec![ClassId(0); amount as usize]),
            num_classes: Cell::new(1),
        }
    }

    pub fn set_all_not_equals(&self) {
        let mut vec = self.vec.borrow_mut();
        for idx in 0..vec.len() {
            vec[idx] = ClassId::from(idx as u32);
        }
        self.num_classes.set(vec.len() as u32);
    }

    pub fn makeset(&self) -> ClassId {
        let mut vec = self.vec.borrow_mut();
        let len = vec.len();
        let id = ClassId(len.try_into().unwrap());
        vec.push(id);
        self.num_classes.set(self.num_classes.get() + 1);
        id
    }

    pub fn num_class_ids(&self) -> u32 {
        self.vec.borrow().len().try_into().unwrap()
    }

    pub fn num_classes(&self) -> u32 {
        self.num_classes.get()
    }

    pub fn find(&self, mut id: ClassId) -> ClassId {
        while id != self.parent(id) {
            self.set_parent(id, self.parent(self.parent(id)));
            id = self.parent(id);
        }
        id
    }

    #[inline]
    fn parent(&self, id: ClassId) -> ClassId {
        self.vec.borrow()[id.0 as usize]
    }

    #[inline]
    fn set_parent(&self, id: ClassId, parent: ClassId) {
        self.vec.borrow_mut()[id.0 as usize] = parent;
    }

    pub fn merge(&self, mut x: ClassId, mut y: ClassId) -> ClassId {
        let mut changed = false;
        while self.parent(x) != self.parent(y) {
            if self.parent(x) > self.parent(y) {
                if x == self.parent(x) {
                    self.set_parent(x, self.parent(y));
                    changed = true;
                    break;
                }
                let z = self.parent(x);
                self.set_parent(x, self.parent(y));
                x = z;
            } else {
                if y == self.parent(y) {
                    self.set_parent(y, self.parent(x));
                    changed = true;
                    break;
                }
                let z = self.parent(y);
                self.set_parent(y, self.parent(x));
                y = z;
            }
        }
        if changed {
            self.num_classes.set(self.num_classes.get() - 1);
        }
        self.parent(x)
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
        assert_eq!(uf.merge(x, y), x);
        assert_eq!(uf.find(x), uf.find(y));
        assert_ne!(uf.find(x), uf.find(z));
        assert_eq!(uf.num_classes(), 2);
        assert_eq!(uf.merge(x, z), x);
        assert_eq!(uf.find(x), uf.find(z));
        assert_eq!(uf.find(y), uf.find(z));
        assert_eq!(uf.find(y), uf.find(x));
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
