pub fn maximum_score(a: i64, b: i64, c: i64) -> i64 {
    let sum = a + b + c;

    let mut max = a;
    if b > max {
        max = b;
    }
    if c > max {
        max = c;
    }

    let rest = sum - max;

    if max >= rest {
        rest
    } else {
        sum / 2
    }
}
