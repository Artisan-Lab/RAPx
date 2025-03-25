/*
 * This is a buggy case: use-after-free
 */
struct Data {
    value: Box<i32>,
}

impl Data {
    fn new(value: i32) -> Data {
        Data {
            value: Box::new(value),
        }
    }

    fn print_value(&self) {
        println!("Value: {}", self.value);
    }
}

fn main() {
    let data_ptr: *const Data;

    {
        let data = Data::new(42);
        data_ptr = &data as *const Data;
    }

    unsafe {
        (*data_ptr).print_value();
    }
}
