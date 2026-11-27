pub fn sum_base(n: i64, k: i64) -> i64 {
    let mut x = n;
    let mut sum = 0;
    while x > 0 {
        sum += x % k;
        x /= k;
    }
    sum
}
