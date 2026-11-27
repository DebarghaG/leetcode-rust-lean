fn is_good(mut x: i64) -> bool {
    let mut valid: bool = true;
    let mut changed: bool = false;

    while x > 0 {
        let d = x % 10;

        if d == 3 || d == 4 || d == 7 {
            valid = false;
            x = 0;
        } else {
            if d == 2 || d == 5 || d == 6 || d == 9 {
                changed = true;
            }
            x = x / 10;
        }
    }

    valid && changed
}

pub fn rotated_digits(n: i64) -> i64 {
    let mut count: i64 = 0;
    let mut i: i64 = 1;

    while i <= n {
        if is_good(i) {
            count = count + 1;
        }
        i = i + 1;
    }

    count
}
