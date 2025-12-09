fn foo1(x: i32) -> i32 {
    let a = x + 1;
    let y = x;
    let mut result = 3;
    if a >= y {
        result =  1;
    } else {
        result =  0;
    }
    return result;
}

fn main(){
    let y = 2;
    let x = y;
    foo1(2);
}