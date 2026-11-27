pub fn longest_repeating_substring(s: &[u8]) -> i64 {
    let n: usize = s.len();

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j <= n {
            row.push(0);
            j += 1;
        }
        dp.push(row);
        i += 1;
    }

    let mut best: i64 = 0;

    let mut i: usize = n;
    while i > 0 {
        i -= 1;

        let mut j: usize = n;
        while j > 0 {
            j -= 1;

            if i != j && s[i] == s[j] {
                let val: i64 = dp[i + 1][j + 1] + 1;
                dp[i][j] = val;
                if val > best {
                    best = val;
                }
            } else {
                dp[i][j] = 0;
            }
        }
    }

    best
}
