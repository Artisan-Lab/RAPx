use std::cell::UnsafeCell;

pub struct RwLock<T: ?Sized> {
    val: UnsafeCell<T>,
}

pub struct RwLockReadGuard<R> {
    inner: R,
}

impl<T> RwLock<T> {
    fn try_read(&self) -> RwLockReadGuard<&RwLock<T>> {
        RwLockReadGuard {
            inner: self
        }
    }
}

impl<R> Drop for RwLockReadGuard<R> {
    fn drop(&mut self) {
        println!("dropping guard");
    }
}

fn main() {
    let rw = RwLock {
        val: UnsafeCell::new(Box::new(1)),
    };
    rw.try_read();
}
