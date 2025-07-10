// testcase for the path constraints analysis
fn countdown(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        countdown(n - 1)
    }
}

fn main() {
    let x = 5;
    let result = countdown(x);

}