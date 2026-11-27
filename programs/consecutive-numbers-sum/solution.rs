pub fn consecutive_numbers_sum(n: i64) -> i64 {
    let mut count: i64 = 0;
    let mut d: i64 = 1;

    while d * d <= n {
        if n % d == 0 {
            if d % 2 == 1 {
                count += 1;
            }

            let q = n / d;
            if q != d && q % 2 == 1 {
                count += 1;
            }
        }
        d += 1;
    }

    count
}
