use std::rc::Rc;

fn test1() {
    let mut x = {
        Rc::<usize>::new_uninit()
    };
    Rc::get_mut(&mut x).unwrap().write(5);
    let y = unsafe { x.assume_init() };
}

fn test2() {
    let mut x = {
        Rc::<usize>::new_uninit()
    };
    // Rc::get_mut(&mut x).unwrap().write(5);
    let y = unsafe { x.assume_init() };
}

fn main() {
}