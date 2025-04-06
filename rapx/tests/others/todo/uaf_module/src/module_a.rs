pub fn drop_vec_ptr<T>(ptr: *mut Vec<T>) {
    unsafe {
        std::ptr::drop_in_place(ptr);
    }
}
