pub fn max_palindromes(s: &[u8], k: i64) -> i64 {
    let n = s.len();
    let kk = k as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i <= n {
        dp.push(0);
        i += 1;
    }

    let mut center = 0usize;
    while center < n {
        // Option to skip s[center].
        if dp[center] > dp[center + 1] {
            dp[center + 1] = dp[center];
        }

        // Odd-length palindromes centered at center.
        let mut l = center;
        let mut r = center;
        while r < n {
            if s[l] != s[r] {
                break;
            }

            let len = r - l + 1;
            if len >= kk {
                let cand = dp[l] + 1;
                if cand > dp[r + 1] {
                    dp[r + 1] = cand;
                }
            }

            if l == 0 {
                break;
            }
            l -= 1;
            r += 1;
        }

        // Even-length palindromes centered between center and center + 1.
        l = center;
        r = center + 1;
        while r < n {
            if s[l] != s[r] {
                break;
            }

            let len = r - l + 1;
            if len >= kk {
                let cand = dp[l] + 1;
                if cand > dp[r + 1] {
                    dp[r + 1] = cand;
                }
            }

            if l == 0 {
                break;
            }
            l -= 1;
            r += 1;
        }

        center += 1;
    }

    dp[n]
}
