#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

pub struct Iterator {
    ptr: *const Vec<i32>,
    ind: usize,
}

impl Iterator {
    pub fn new(pl: *const Vec<i32>) -> Self {
        Iterator { ptr: pl, ind: 0 }
    }
}

pub struct PropList {
    ptr: Box<Vec<i32>>,
}

impl PropList {
    pub fn iter_prop(&self) -> Iterator {
        let raw_ptr = &(*self.ptr) as *const Vec<i32>;
        Iterator::new(raw_ptr)
    }
}
