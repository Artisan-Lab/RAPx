use std::marker::PhantomData;
use std::ptr;

struct Proxy1<T> {
    _p: *mut T,
}


struct Proxy2<T> {
    _p: *mut T,
    _marker: PhantomData<T>,
}

struct Proxy3<'a, T> {
    _p: *mut T,
    _marker: PhantomData<&'a T>,
}

impl<T> Drop for Proxy1<T> {
    fn drop(&mut self) {
        println!("Proxy1 dropped!");
    }
}
impl<T> Drop for Proxy2<T> {
    fn drop(&mut self) {
        println!("Proxy2 dropped!");
    }
}
impl<'a, T> Drop for Proxy3<'a, T> {
    fn drop(&mut self) {
        println!("Proxy3 dropped!");
    }
}
fn main() {
    let buf = Box::new("buffer");
    let ptr = Box::into_raw(buf);
    let _proxy1 = Proxy1 { _p:ptr };
    let _proxy2 = Proxy2 { _p:ptr, _marker: PhantomData };
    let _proxy3 = Proxy3 { _p:ptr, _marker: PhantomData };
}
