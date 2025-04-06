#![feature(box_as_ptr)]

use std::slice;
struct St1 { ptr: *mut u8, len: usize }
struct St2 { ptr: *mut u8, len: usize }
impl St1 {
    pub fn from(p: *mut u8, l: usize) -> St1 {
        St1 { ptr: p, len: l }
    }
    
    pub unsafe fn get(&self) -> &[u8] {
        slice::from_raw_parts(self.ptr, self.len)
    }
}
impl St2 {
    pub unsafe fn from(p: *mut u8, l: usize) -> St2 {
        St2 { ptr: p, len: l }
    }
    pub fn get(&self, x: usize) -> u8 {
        if x < self.len {
            unsafe { *self.ptr.offset(x as isize) }
        } else {
            0
        }
    }
}
unsafe fn f1(p: *mut u8, l: usize) {
    let s1 = St1::from(p, l); 
    f2(&s1); 
}
unsafe fn f2(s1: &St1) {
    let t1 = unsafe { s1.get() };
    let s2 = unsafe { St2::from(s1.ptr, s1.len)};
    let t2 = s2.get(0);
    assert_eq!(t1[0], t2);
}

fn main() {
    //let p = &mut 0_u8 as *mut u8;
    let p = Box::as_mut_ptr(&mut Box::new(0_u8));
    //let p = { vec!(0_u8).as_mut_ptr() as *mut u8 };
    unsafe {f1(p, 1)};
}
