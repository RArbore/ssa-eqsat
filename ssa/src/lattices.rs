use core::cell::RefCell;
use core::cmp::{max, min};
use core::hash::Hash;
use core::marker::PhantomData;
use std::collections::HashMap;
use std::i32;

use ds::table::Value;
use imp::term::{BinaryOp, UnaryOp};

#[derive(Debug)]
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

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Interval {
    pub(crate) low: i32,
    pub(crate) high: i32,
}

impl Interval {
    pub fn top() -> Interval {
        Interval {
            low: i32::MIN,
            high: i32::MAX,
        }
    }

    pub fn bottom() -> Interval {
        Interval {
            low: i32::MAX,
            high: i32::MIN,
        }
    }

    pub fn union(&self, other: &Interval) -> Interval {
        Interval {
            low: min(self.low, other.low),
            high: max(self.high, other.high),
        }
    }

    pub fn intersect(&self, other: &Interval) -> Interval {
        Interval {
            low: max(self.low, other.low),
            high: min(self.high, other.high),
        }
    }

    pub fn widen(&self, new: &Interval) -> Interval {
        Interval {
            low: if self.low > new.low {
                i32::MIN
            } else {
                self.low
            },
            high: if self.high < new.high {
                i32::MAX
            } else {
                self.high
            },
        }
    }

    pub fn try_constant(&self) -> Option<i32> {
        if self.low == self.high {
            Some(self.low)
        } else {
            None
        }
    }

    pub fn forward_unary(&self, op: UnaryOp) -> Interval {
        use UnaryOp::*;
        (|| match op {
            Negate => Some(Interval {
                low: self.high.checked_neg()?,
                high: self.low.checked_neg()?,
            }),
            Not => Some({
                if self.low == 0 && self.high == 0 {
                    Interval { low: 1, high: 1 }
                } else if self.low > 0 || self.high < 0 {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
        })()
        .unwrap_or(Interval::top())
    }

    pub fn forward_binary(&self, other: &Interval, op: BinaryOp) -> Interval {
        use BinaryOp::*;
        (|| match op {
            Add => Some(Interval {
                low: self.low.checked_add(other.low)?,
                high: self.high.checked_add(other.high)?,
            }),
            Sub => Some(Interval {
                low: self.low.checked_sub(other.high)?,
                high: self.high.checked_sub(other.low)?,
            }),
            Mul => Some(Interval {
                low: min(
                    min(
                        self.low.checked_mul(other.low)?,
                        self.low.checked_mul(other.high)?,
                    ),
                    min(
                        self.high.checked_mul(other.low)?,
                        self.high.checked_mul(other.high)?,
                    ),
                ),
                high: max(
                    max(
                        self.low.checked_mul(other.low)?,
                        self.low.checked_mul(other.high)?,
                    ),
                    max(
                        self.high.checked_mul(other.low)?,
                        self.high.checked_mul(other.high)?,
                    ),
                ),
            }),
            Div => todo!(),
            Rem => todo!(),
            EE => Some({
                if let (Some(cons1), Some(cons2)) = (self.try_constant(), other.try_constant())
                    && cons1 == cons2
                {
                    Interval { low: 1, high: 1 }
                } else if self.high < other.low || other.high < self.low {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            NE => Some({
                if let (Some(cons1), Some(cons2)) = (self.try_constant(), other.try_constant())
                    && cons1 == cons2
                {
                    Interval { low: 0, high: 0 }
                } else if self.high < other.low || other.high < self.low {
                    Interval { low: 1, high: 1 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            LT => Some({
                if self.high < other.low {
                    Interval { low: 1, high: 1 }
                } else if self.low >= other.high {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            LE => Some({
                if self.high <= other.low {
                    Interval { low: 1, high: 1 }
                } else if self.low > other.high {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            GT => Some({
                if self.low > other.high {
                    Interval { low: 1, high: 1 }
                } else if self.high <= other.low {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
            GE => Some({
                if self.low >= other.high {
                    Interval { low: 1, high: 1 }
                } else if self.high < other.low {
                    Interval { low: 0, high: 0 }
                } else {
                    Interval { low: 0, high: 1 }
                }
            }),
        })()
        .unwrap_or(Interval::top())
    }
}

impl Interner<Interval> {
    pub fn merge(&self) -> impl FnMut(Value, Value) -> Value + '_ {
        |a: Value, b: Value| {
            self.intern(self.get(a.into()).intersect(&self.get(b.into())))
                .into()
        }
    }
}
