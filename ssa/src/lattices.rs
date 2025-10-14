use core::cell::RefCell;
use core::cmp::{max, min};
use core::hash::Hash;
use core::marker::PhantomData;
use std::collections::HashMap;

pub struct InternId<T> {
    id: u32,
    _phantom: PhantomData<T>,
}

impl<T> Clone for InternId<T> {
    fn clone(&self) -> Self {
        Self {
            id: self.id.clone(),
            _phantom: self._phantom.clone(),
        }
    }
}

impl<T> Copy for InternId<T> {}

impl<T> PartialEq for InternId<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T> Eq for InternId<T> {}

impl<T> Hash for InternId<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<T> From<u32> for InternId<T> {
    fn from(value: u32) -> Self {
        InternId {
            id: value,
            _phantom: PhantomData,
        }
    }
}

impl<T> From<InternId<T>> for u32 {
    fn from(value: InternId<T>) -> Self {
        value.id
    }
}

pub struct Interner<T> {
    obj_to_id: RefCell<HashMap<T, InternId<T>>>,
    id_to_obj: RefCell<Vec<T>>,
}

impl<T: Clone + PartialEq + Eq + Hash> Interner<T> {
    pub fn new() -> Self {
        Self {
            obj_to_id: RefCell::new(HashMap::new()),
            id_to_obj: RefCell::new(vec![]),
        }
    }

    pub fn intern(&self, t: T) -> InternId<T> {
        let mut obj_to_id = self.obj_to_id.borrow_mut();
        let mut id_to_obj = self.id_to_obj.borrow_mut();
        if let Some(id) = obj_to_id.get(&t) {
            *id
        } else {
            let id = InternId {
                id: id_to_obj.len() as u32,
                _phantom: PhantomData,
            };
            obj_to_id.insert(t.clone(), id);
            id_to_obj.push(t);
            id
        }
    }

    pub fn get(&self, id: InternId<T>) -> T {
        self.id_to_obj.borrow()[id.id as usize].clone()
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Interval {
    pub(crate) low: i32,
    pub(crate) high: i32,
}

impl Interval {
    pub fn bottom() -> Interval {
        Interval {
            low: i32::MIN,
            high: i32::MAX,
        }
    }

    pub fn union(&self, other: &Interval) -> Interval {
        Interval {
            low: min(self.low, other.low),
            high: min(self.high, other.high),
        }
    }

    pub fn intersect(&self, other: &Interval) -> Interval {
        Interval {
            low: max(self.low, other.low),
            high: max(self.high, other.high),
        }
    }

    pub fn try_constant(&self) -> Option<i32> {
        if self.low == self.high {
            Some(self.low)
        } else {
            None
        }
    }
}
