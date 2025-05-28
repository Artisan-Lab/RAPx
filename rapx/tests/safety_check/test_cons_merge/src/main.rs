#![feature(box_as_ptr)]
use std::slice;
struct St1 { ptr: *mut u8, len: usize }
impl St1 {
    pub fn from(p: *mut u8, l: usize) -> St1 {
        St1 { ptr: p, len: l }
    }
    
    pub unsafe fn get(&self) -> &[u8] {
        unsafe{
            slice::from_raw_parts(self.ptr, self.len) // ptr maybe unaligned and null
        }
    }

    pub unsafe fn modify(&mut self) {
        self.len = 1;
    }
}

unsafe fn f1(p: *mut u8, l: usize) {
    let mut s1 = St1::from(p, l); 
    unsafe {
        s1.get();
        s1.modify();
    }
}

fn main() {
    let p = Box::as_mut_ptr(&mut Box::new(0_u8));
    unsafe {f1(p, 1)};
}