pub fn is_match(s: &[u8], p: &[u8]) -> bool {
    let n = s.len();
    let m = p.len();

    // dp[j] currently represents dp[i][j] (whether s[0..i] matches p[0..j]).
    // We roll over i, so the array is reused each row.
    let mut dp: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k <= m {
        dp.push(false);
        k += 1;
    }

    // Base row i = 0: empty string vs pattern prefix.
    dp[0] = true;
    let mut j: usize = 1;
    while j <= m {
        if p[j - 1] == b'*' {
            dp[j] = dp[j - 1];
        }
        j += 1;
    }

    let mut i: usize = 1;
    while i <= n {
        // diag holds dp[i-1][j-1] for the current j.
        let mut diag: bool = dp[0]; // dp[i-1][0]
        dp[0] = false;              // dp[i][0] = false for i > 0
        let mut jj: usize = 1;
        while jj <= m {
            let old: bool = dp[jj]; // dp[i-1][jj]
            if p[jj - 1] == b'*' {
                // dp[i][jj] = dp[i-1][jj] || dp[i][jj-1]
                dp[jj] = old || dp[jj - 1];
            } else if p[jj - 1] == b'?' || p[jj - 1] == s[i - 1] {
                // dp[i][jj] = dp[i-1][jj-1]
                dp[jj] = diag;
            } else {
                dp[jj] = false;
            }
            diag = old;
            jj += 1;
        }
        i += 1;
    }

    dp[m]
}
