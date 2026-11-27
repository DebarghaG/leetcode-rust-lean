pub fn distribute_candies(n: i64, limit: i64) -> i64 {
    let mut ways: i64 = 0;
    let mut a: i64 = 0;

    while a <= limit && a <= n {
        let mut b: i64 = 0;
        while b <= limit && b <= n - a {
            let c: i64 = n - a - b;
            if c >= 0 && c <= limit {
                ways += 1;
            }
            b += 1;
        }
        a += 1;
    }

    ways
}
