fn main() {
    let mut value = 0i32;
    let ptr: *mut i32 = &mut value as *mut i32;
    unsafe {
        *ptr = 1;
    }
}

