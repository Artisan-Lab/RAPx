
/// Will pass because alignment of ptr must be 2
/// and offset is 2, so the pointer is still aligned.
fn test<T>(data: &[T], offset:usize) {
    let ptr = data.as_ptr(); 
    if ptr as usize % 2 == 0 
        && ptr as usize % 4 != 0 // These conditions mean ptr's alignment must be 2
        && offset % 2 == 0 // then byte offset 2, the ptr is still aligned
    {
        let sound_ptr = unsafe { ptr.byte_add(offset) };
        let value = unsafe { sound_ptr.read() };
    }
}

/// Will fail because alignment of ptr could be 2, 4, 8...
/// and offset is 2, so the pointer could be unaligned.
fn test2<T>(data: &[T], offset:usize) {
    let ptr = data.as_ptr(); 
    if ptr as usize % 2 == 0 
        // && ptr as usize % 4 != 0 // This line has been commented out, so ptr's alignment could be 2, 4, 8... 
        && offset % 2 == 0 // then byte offset 2, the ptr could be unaligned when ptr is aligned to 4 or more
    {
        let unsound_ptr = unsafe { ptr.byte_add(offset) };
        let value = unsafe { unsound_ptr.read() };
    }
}


/// Pass for aligned pointers check
fn test3<T>(ptr: *mut T) {
    if ptr.is_aligned() { // ptr is aligned
        unsafe {
            let _value = unsafe { ptr.read() }; // aligned ptr read
        }
    }
}

/// Fail for unaligned pointers check
fn test4<T>(ptr: *mut T) {
    if !ptr.is_aligned() { // ptr is unaligned
        unsafe {
            let _value = unsafe { ptr.read() }; // unaligned ptr read
        }
    }
}

fn main() {
}