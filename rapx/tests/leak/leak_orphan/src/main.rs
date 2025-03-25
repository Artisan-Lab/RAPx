fn main() {
    let buf = Box::new("buffer");
    let _ptr = Box::into_raw(buf);
}
