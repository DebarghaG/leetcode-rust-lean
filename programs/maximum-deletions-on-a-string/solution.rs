pub fn delete_string(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut t = 0;
    while t < n + 1 {
        dp.push(0);
        t += 1;
    }

    let mut next: Vec<i64> = Vec::new();
    t = 0;
    while t < n + 1 {
        next.push(0);
        t += 1;
    }

    let mut i = n;
    while i > 0 {
        i -= 1;

        let mut curr: Vec<i64> = Vec::new();
        t = 0;
        while t < n + 1 {
            curr.push(0);
            t += 1;
        }

        let mut j = n;
        while j > i + 1 {
            j -= 1;
            if s[i] == s[j] {
                curr[j] = next[j + 1] + 1;
            }
        }

        let mut best: i64 = 1;
        let max_k = (n - i) / 2;
        let mut k: usize = 1;
        let mut kk: i64 = 1;

        while k <= max_k {
            if curr[i + k] >= kk {
                let cand = dp[i + k] + 1;
                if cand > best {
                    best = cand;
                }
            }
            k += 1;
            kk += 1;
        }

        dp[i] = best;
        next = curr;
    }

    dp[0]
}
