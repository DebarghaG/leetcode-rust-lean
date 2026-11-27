pub fn minimum_substrings_in_partition(s: &[u8]) -> i64 {
    let n: usize = s.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        dp.push(0);
        i += 1;
    }

    dp[0] = 0;

    let mut end: usize = 1;
    while end <= n {
        let mut cnt: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < 26 {
            cnt.push(0);
            c += 1;
        }

        let mut distinct: i64 = 0;
        let mut max_freq: i64 = 0;
        let mut best: i64 = (n as i64) + 1;

        let mut start: usize = end;
        while start > 0 {
            start = start - 1;

            let ch: usize = (s[start] - b'a') as usize;
            let old: i64 = cnt[ch];
            cnt[ch] = old + 1;

            if old == 0 {
                distinct += 1;
            }
            if cnt[ch] > max_freq {
                max_freq = cnt[ch];
            }

            let len: i64 = (end - start) as i64;
            if len == distinct * max_freq {
                let candidate: i64 = dp[start] + 1;
                if candidate < best {
                    best = candidate;
                }
            }
        }

        dp[end] = best;
        end += 1;
    }

    dp[n]
}
