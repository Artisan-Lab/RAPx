#![allow(unused)]

enum Selector {
    First,
    Second,
}

// Expected alias analysis result: (0, 1) (0, 2)
fn foo(x: *mut i32, y: *mut i32, choice: Selector) -> *mut i32 {
    let mut r = x;
    let mut q = x;

    unsafe {
        while *r > 0 {
            let mut p = match choice {
                Selector::First => y,
                Selector::Second => x,
            };

            loop {
                r = q;
                q = match choice {
                    Selector::First => x,
                    Selector::Second => p,
                };
                *q -= 1;
                if *r <= 1 {
                    break;
                }
                q = y;
            }

            if *r == 0 {
                break;
            }
        }
    }

    r
}
