fn foo1(x: i32) -> i32 {
    let a = x + 1;
    let y = x;
    let mut result ;
    let _b = a - y; // _11/_8. [1,1] can be inferred before range analysis
    if a >= y {    // always true
        result =  a;
    } else {
        result =  y;
    }
    return result;  // result is always a, but its upper/lower bound 
                    // symbexpr is hard to be inferred without range analysis
}


fn main(){
    let y = 2;
    let x = y;
    foo1(2);
}