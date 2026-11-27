pub fn min_operations(n: i64) -> i64 {
    let half = n / 2;
    half * (n - half)
}
