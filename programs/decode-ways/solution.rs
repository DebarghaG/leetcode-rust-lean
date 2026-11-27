pub fn num_decodings(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= n {
        dp.push(0);
        k += 1;
    }

    dp[0] = 1;
    let mut i: usize = 1;
    while i <= n {
        let cur = s[i - 1];
        if cur != b'0' {
            dp[i] = dp[i] + dp[i - 1];
        }

        if i >= 2 {
            let first = s[i - 2];
            let second = s[i - 1];
            if first == b'1' || (first == b'2' && second <= b'6') {
                dp[i] = dp[i] + dp[i - 2];
            }
        }

        i += 1;
    }

    dp[n]
}
