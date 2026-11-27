pub fn first_day_been_in_all_rooms(nextVisit: &[i64]) -> i64 {
    let md: i64 = 1000000007;
    let n = nextVisit.len();

    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    dp.push(0);

    let mut i: usize = 1;
    while i < n {
        let idx = nextVisit[i - 1] as usize;
        let prev: i64;
        if idx < i {
            prev = dp[idx];
        } else {
            prev = 0;
        }

        let cur = (2 * dp[i - 1] - prev + 2 + md) % md;
        dp.push(cur);

        i += 1;
    }

    dp[n - 1]
}
