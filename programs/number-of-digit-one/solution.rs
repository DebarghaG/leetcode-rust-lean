pub fn count_digit_one(n: i64) -> i64 {
    let mut count: i64 = 0;
    let mut factor: i64 = 1;

    while factor <= n {
        let high: i64 = n / (factor * 10);
        let cur: i64 = (n / factor) % 10;
        let low: i64 = n % factor;

        if cur == 0 {
            count += high * factor;
        } else if cur == 1 {
            count += high * factor + low + 1;
        } else {
            count += (high + 1) * factor;
        }

        factor *= 10;
    }

    count
}
