use std::mem::MaybeUninit;

fn main() {
    let mut x = MaybeUninit::<Box<u8>>::uninit();
    x.write(Box::new(1));
    
    unsafe {
        x.assume_init_drop();
        x.assume_init();
    }
}
