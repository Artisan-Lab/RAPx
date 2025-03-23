struct Proxy<T> {
    _p: *mut T,
}

fn main() {
    let buf = Box::new("buffer");
    let ptr = Box::into_raw(buf);
    let _proxy = Proxy { _p: ptr };
}
