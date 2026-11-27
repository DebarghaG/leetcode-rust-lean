pub fn trailing_zeroes(n: i64) -> i64 {
    let mut count: i64 = 0;
    let mut m: i64 = n;
    while m > 0 {
        m = m / 5;
        count = count + m;
    }
    count
}
