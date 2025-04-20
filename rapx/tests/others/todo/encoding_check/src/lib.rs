use std::str;

fn foo_1(mut n: u128, base: usize, output: &mut String) {
    const BASE_64: &[u8; 64] = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ@$";
    let mut s = [0u8; 128];
    let mut index = s.len();
    let base = base as u128;
    loop {
        index -= 1;
        s[index] = BASE_64[(n % base) as usize];
        n /= base;
        if n == 0 {
            break;
        }
    }
    output.push_str(str::from_utf8(&s[index..]).unwrap());
}

static CHARS: &[u8; 5] = b"12345";

fn foo_2() -> String {
    let mut v = Vec::with_capacity(12);
    v.push(CHARS[2 as usize]);
    v.push(CHARS[3 as usize]);
    v.push(b' ');
    String::from_utf8_lossy(&v).to_string()
}
