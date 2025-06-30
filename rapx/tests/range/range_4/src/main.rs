// fn test1() {
//     let mut x = 0;

//     while x < 10 {
//         x += 1;
//     }
// }
pub struct SSAstmt;
pub struct ESSAstmt;

#[used]
static _SSAstmt: Option<SSAstmt> = None;
static _ESSAstmt: Option<ESSAstmt> = None;

fn main(){
    let foo2_param = 10;
    let foo3_param = 20;
    foo1();
    foo2(foo2_param);
    foo3(foo3_param);
    let mut x = foo4(foo3_param);
}
fn foo1() {
    let mut k = 0;

    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        }
        
    }
}
fn foo2(k:i32) {

    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        }
        
    }
}
fn foo3(k:i32) {

    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        }
        
    }
    foo2(k+1)
}
fn foo4(k:i32) -> i32 {
    let mut j = 0;
    while j < k {
        j+=1;
    }
    return j;

}