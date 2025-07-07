pub struct SSAstmt;
pub struct ESSAstmt;

fn main() {
    let para1 = 42;
    foo1(para1);

    let para2 = 52;
    let _x = foo2(55, para2);

}
// This function tests passing ranges of parameters between functions.
fn foo1(mut k: usize) {
    while k < 100 {
        k += 1;
    }
}
// This function tests whether the range of returned value is processed as expected.
fn foo2(mut k: usize, _c: usize) -> usize {
    while k < 100 {
        k += 1;
    }
    k
}
