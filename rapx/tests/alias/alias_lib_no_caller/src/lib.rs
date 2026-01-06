#[allow(dead_code)]
struct Item<'a> {
    ptr: &'a str,
}

#[allow(dead_code)]
#[derive(Debug)]
struct Iter {
    ptr: *const str,
}

impl<'a> Iter {
    #[allow(dead_code)]
    fn new(item: Item<'a>) -> Iter {
        Iter { ptr: item.ptr }
    }
}
