use std::slice;
pub struct SSAstmt;
pub struct ESSAstmt;

fn main() {
    let mut buf = vec![10u8, 20, 30];
    let ptr = buf.as_mut_ptr();
    let len = buf.len();

    let slice = unsafe { slice::from_raw_parts(ptr, len) };

    for i in 0..len {
        println!("slice[{}] = {}", i, slice[i]);
    }
    let index = len; 
    let _val = slice[index];
    buf[1] += 1;
}
