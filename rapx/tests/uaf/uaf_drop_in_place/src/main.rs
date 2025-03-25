#![feature(fn_traits)]
use std::ptr::drop_in_place;
fn main() {
    let mut x = Box::from(0);
    let ptr = &mut x as *mut Box<i32>;
    drop(x);
    unsafe {
        drop_in_place(ptr);
    }
}
