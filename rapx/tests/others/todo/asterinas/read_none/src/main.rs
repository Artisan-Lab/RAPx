use std::cell::UnsafeCell;


fn main() {
    let c:UnsafeCell<Option<Box<i32>>> = UnsafeCell::new(None);

    unsafe {
        let ptr = c.get();
        debug_assert!(ptr.read().is_none());
        ptr.write(Some(Box::new(1)));
    }
}
