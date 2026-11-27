fn is_self_dividing(n: i64) -> bool {
    let mut x = n;
    while x > 0 {
        let d = x % 10;
        if d == 0 {
            return false;
        }
        if n % d != 0 {
            return false;
        }
        x = x / 10;
    }
    true
}

pub fn self_dividing_numbers(left: i64, right: i64) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut n = left;
    while n <= right {
        if is_self_dividing(n) {
            out.push(n);
        }
        n += 1;
    }
    out
}
