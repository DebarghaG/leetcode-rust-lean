pub fn min_steps(n: i64) -> i64 {
    let mut m = n;
    let mut ans = 0;
    let mut d = 2;

    while d * d <= m {
        while m % d == 0 {
            ans += d;
            m /= d;
        }
        d += 1;
    }

    if m > 1 {
        ans += m;
    }

    ans
}
