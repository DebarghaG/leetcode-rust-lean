pub fn is_three(n: i64) -> bool {
    if n < 1 {
        return false;
    }

    let mut count: i64 = 0;
    let mut d: i64 = 1;

    while d <= n {
        if n % d == 0 {
            count += 1;
        }
        d += 1;
    }

    count == 3
}
