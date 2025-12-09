/*
 * The auditing graph should contain entry from the safe caller to the unsafe callee.
 * */
fn main() {
    let mut s = String::from("a tmp string");
    let ptr = s.as_mut_ptr();
    let _v = unsafe { Vec::from_raw_parts(ptr, s.len(), s.len()) };
}

