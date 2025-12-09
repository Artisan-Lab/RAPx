use core::mem;

pub struct Wrapper {
    data: String,
}

impl Wrapper {
    pub fn new(data: String) -> Self {
        Self {
            data
        }
    }
            
    pub fn replace_with(&mut self, new_data: String) -> String {
        mem::replace(&mut self.data, new_data)
    }

    pub fn display(&self) {
        println!("{}", self.data);
    }
}

pub fn main() {
    let hello = "hello".to_owned();
    let world = "world".to_owned();
    let mut wrapper = Wrapper::new(hello);
    wrapper.display();
    let original_hello = wrapper.replace_with(world);
    wrapper.display();
    println!("{}", original_hello);
}
