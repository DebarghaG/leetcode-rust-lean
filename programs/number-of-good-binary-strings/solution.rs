pub fn good_binary_strings(minLength: i64, maxLength: i64, oneGroup: i64, zeroGroup: i64) -> i64 {
    let modv: i64 = 1000000007;

    let min_len = minLength as usize;
    let max_len = maxLength as usize;
    let one = oneGroup as usize;
    let zero = zeroGroup as usize;

    let mut dp: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i <= max_len {
        if i == 0 {
            dp.push(1);
        } else {
            let mut ways: i64 = 0;

            if i >= zero {
                ways = ways + dp[i - zero];
            }
            if i >= one {
                ways = ways + dp[i - one];
            }

            ways = ways % modv;
            dp.push(ways);
        }

        i += 1;
    }

    let mut ans: i64 = 0;
    let mut len = min_len;
    while len <= max_len {
        ans = ans + dp[len];
        ans = ans % modv;
        len += 1;
    }

    ans
}
