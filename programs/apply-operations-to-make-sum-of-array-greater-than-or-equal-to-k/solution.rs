pub fn min_operations(k: i64) -> i64 {
    let mut best: i64 = k - 1;
    let mut x: i64 = 1;

    while x <= k {
        let copies: i64 = (k + x - 1) / x;
        let operations: i64 = (x - 1) + (copies - 1);
        if operations < best {
            best = operations;
        }
        x += 1;
    }

    best
}
