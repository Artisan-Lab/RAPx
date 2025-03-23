use std::marker::PhantomData;

struct Proxy1<T> {
    p: *mut T,
}

struct Proxy2<T> {
    p: *mut T,
    _marker: PhantomData<T>,
}

impl<T> Drop for Proxy2<T> {
    fn drop(&mut self) {}
}

fn main() {
    let buf = Box::new("buffer");
    let ptr = Box::into_raw(buf);
    let _proxy1 = Proxy1 { p: ptr };
    let _proxy2 = Proxy2 {
        p: ptr,
        _marker: PhantomData,
    };
}
