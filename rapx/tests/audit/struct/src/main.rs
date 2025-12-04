#![feature(box_as_ptr)]
#![allow(dead_code)]

use std::slice;
struct St1 { pub ptr: *mut u8, len: usize }
struct St2 { pub ptr: *mut u8, pub len: usize }
impl St1 {
    pub fn from(p: *mut u8, l: usize) -> St1 {
        St1 { ptr: p, len: l }
    }
    
    pub unsafe fn get(&self) -> &[u8] {
        slice::from_raw_parts(self.ptr, self.len)
    }

    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = 1;
    }
}

impl St2 {
    pub unsafe fn from(p: *mut u8, l: usize) -> St2 {
        St2 { ptr: p, len: l }
    }
    pub unsafe fn get(&self) -> &[u8] {
        slice::from_raw_parts(self.ptr, self.len)
    }
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = 1;
    }
}

fn main() {
    let p = Box::as_mut_ptr(&mut Box::new(0_u8));
    let s1 = St1::from(p, 1); 
}
