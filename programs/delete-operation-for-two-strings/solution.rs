pub fn min_distance(word1: &[u8], word2: &[u8]) -> i64 {
    let n = word1.len();
    let m = word2.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut j = 0;
    while j <= m {
        dp.push(0);
        j += 1;
    }

    let mut i = 0;
    while i < n {
        let mut diag: i64 = 0;
        let mut j = 1;
        while j <= m {
            let old = dp[j];

            if word1[i] == word2[j - 1] {
                dp[j] = diag + 1;
            } else {
                let mut best = dp[j - 1];
                if old > best {
                    best = old;
                }
                dp[j] = best;
            }

            diag = old;
            j += 1;
        }
        i += 1;
    }

    let lcs = dp[m];
    (n as i64) + (m as i64) - 2 * lcs
}
