use std::marker::PhantomData;

//expected result: (0,[0])
struct Proxy1<T> {
    _p: *mut T,
}

//expected result: (1,[0])
struct Proxy2<T> {
    _p: *mut T,
    _marker: PhantomData<T>,
}

//expected result: (0,[0,0])
struct Proxy3<'a, T> {
    _p: *mut T,
    _marker: PhantomData<&'a T>,
}

//expected result: (0,[1])
struct Proxy4<T> {
    _x: T,
}

//expected result: (1,[0])
struct Proxy5<T> {
    _x: Proxy2<T>,
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
    let _p1 = Proxy1 { _p:ptr };
    let mut p2a = Proxy2 { _p:ptr, _marker: PhantomData };
    let p2b = Proxy2 { _p:ptr, _marker: PhantomData };
    let _p3 = Proxy3 { _p: &mut p2a as *mut Proxy2<&str>, _marker: PhantomData };
    let _p4 = Proxy4 { _x: p2a };
    let _p5 = Proxy5 { _x: p2b };
}
