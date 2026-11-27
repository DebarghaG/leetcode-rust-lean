pub fn judge_square_sum(c: i64) -> bool {
    let mut b: i64 = 0;
    while (b + 1) * (b + 1) <= c {
        b += 1;
    }

    let mut a: i64 = 0;
    while a <= b {
        let sum = a * a + b * b;
        if sum == c {
            return true;
        }
        if sum < c {
            a += 1;
        } else {
            b -= 1;
        }
    }

    false
}
