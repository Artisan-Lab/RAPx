struct Item<'a>(&'a str);

#[derive(Debug)]
struct Iter {
    ptr: *const str,
}

impl<'a> Iter {
    fn new(item: Item<'a>) -> Iter {
        Iter { ptr: item.0 }
    }
}

fn main() {
    let x = Item("as");
    let x = Iter::new(x);
    println!("{:?}", x);
}
