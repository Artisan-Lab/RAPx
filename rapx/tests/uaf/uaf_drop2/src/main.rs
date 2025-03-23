use std::env;

#[derive(Debug)]
struct MyRef<'a> {
    a: &'a str,
}

unsafe fn f<'a>(myref: MyRef<'a>) -> MyRef<'static> {
    unsafe { std::mem::transmute(myref) }
}

fn main() {
    let string = "Hello World!".to_string();
    let args: Vec<String> = env::args().collect();
    let my_ref = unsafe { f(MyRef { a: &string }) };
    if args.len() > 2 {
        drop(string);
    }
    println!("{:?}", my_ref.a);
}
