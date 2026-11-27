pub fn number_of_arrays(s: &[u8], k: i64) -> i64 {
    let modulus: i64 = 1000000007;
    let n = s.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut p = 0usize;
    while p <= n {
        dp.push(0);
        p += 1;
    }
    dp[0] = 1;

    let mut i = 0usize;
    while i < n {
        if s[i] != b'0' && dp[i] != 0 {
            let mut j = i;
            let mut value: i64 = 0;

            while j < n {
                let digit = (s[j] - b'0') as i64;
                value = value * 10 + digit;

                if value > k {
                    break;
                }

                let add = dp[i];
                let mut next = dp[j + 1] + add;
                if next >= modulus {
                    next = next - modulus;
                }
                dp[j + 1] = next;

                j += 1;
            }
        }

        i += 1;
    }

    dp[n]
}
