#![feature(allocator_api)]
#[allow(unused)]

use std::alloc::Global;

fn foo(p: *mut u8) -> Vec<u8, Global> {
    unsafe { Vec::from_raw_parts_in(p, 1, 1, Global) }
}
