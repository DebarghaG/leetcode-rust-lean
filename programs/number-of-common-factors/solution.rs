pub fn common_factors(a: i64, b: i64) -> i64 {
    let mut count: i64 = 0;
    let mut x: i64 = 1;
    while x <= a && x <= b {
        if a % x == 0 && b % x == 0 {
            count += 1;
        }
        x += 1;
    }
    count
}
