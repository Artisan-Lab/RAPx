//test ssa_transform
fn main() {
    let mut k = 0;

    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        }

        k += 1;
    }
}
