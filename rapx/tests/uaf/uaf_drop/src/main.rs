use std::mem::ManuallyDrop;

fn main() {
    let mut slot = ManuallyDrop::<Box<u8>>::new(Box::new(1));
    let mut v = ManuallyDrop::<Vec<u8>>::new(Vec::new());
    unsafe {
        ManuallyDrop::drop(&mut slot);
        ManuallyDrop::drop(&mut v);
    }
    println!("{:?}", slot);
    println!("{:?}", v);
}
