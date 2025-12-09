#![allow(unused)]

use std::mem::forget;

fn main() {
    let mut b1 = Box::new(99);
    let p = &mut *b1 as *mut i32;
    let _b2 = unsafe { Box::from_raw(p) }; //
    panic!();
    forget(b1);
}
