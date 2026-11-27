pub fn pivot_integer(n: i64) -> i64 {
    let mut total: i64 = 0;
    let mut i: i64 = 1;
    while i <= n {
        total += i;
        i += 1;
    }

    let mut prefix: i64 = 0;
    let mut x: i64 = 1;
    while x <= n {
        prefix += x;
        let suffix: i64 = total - prefix + x;
        if prefix == suffix {
            return x;
        }
        x += 1;
    }

    -1
}
