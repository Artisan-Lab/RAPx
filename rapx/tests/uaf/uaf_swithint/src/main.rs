use std::mem::ManuallyDrop;
enum A {
    A1,
    A2,
}
fn evil_test(a: A) {
    let mut count = 0;
    let mut slot = ManuallyDrop::<Box<u8>>::new(Box::new(1));
    loop {
        if let A::A1 = a {
            count += 1;
            if count < 2 {
                unsafe {
                    ManuallyDrop::drop(&mut slot);
                    ManuallyDrop::drop(&mut slot);
                }
                continue;
            }
            break;
        } else {
            println!("{:?}", slot);
            unsafe {
                ManuallyDrop::drop(&mut slot);
            }
            break;
        }
    }
}
fn main() {
    let a1 = A::A1;
    let a2 = A::A2;
    evil_test(a1);
    evil_test(a2);
}
