pub fn min_end(n: i64, x: i64) -> i64 {
    let mut ans: i64 = x;
    let mut k: i64 = n - 1;
    let mut mask: i64 = 1;

    while k > 0 {
        if (ans / mask) % 2 == 0 {
            if k % 2 == 1 {
                ans = ans + mask;
            }
            k = k / 2;
        }
        mask = mask * 2;
    }

    ans
}
