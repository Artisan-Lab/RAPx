
pub struct SSAstmt;
pub struct ESSAstmt;
use std::slice;

// testcase for the path constraints analysis
pub fn test7(a: &mut [u8], b: &[u32; 20]) {
    unsafe {
        let c = slice::from_raw_parts_mut(a.as_mut_ptr() as *mut u32, 20);
        for i in 0..20 {
            c[i] ^= b[i];
        }
    }
}

fn main() {
    let mut x = [0u8;40];
    let y = [0u32;20];
    test7(&mut x[1..32], &y);
}
