use std::sync::Arc;
use core::mem;

pub fn main() {
    let hello = Arc::new("hello".to_owned());
    let hello_weak = Arc::downgrade(&hello);
    mem::drop(hello_weak);
    print!("{}", hello);
}