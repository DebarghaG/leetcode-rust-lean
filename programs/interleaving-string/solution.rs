pub fn is_interleave(s1: &[u8], s2: &[u8], s3: &[u8]) -> bool {
    let m = s1.len();
    let n = s2.len();

    if m + n != s3.len() {
        return false;
    }

    let mut dp: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j <= n {
        dp.push(false);
        j += 1;
    }

    dp[0] = true;

    j = 1;
    while j <= n {
        let prev = dp[j - 1];
        if prev && s2[j - 1] == s3[j - 1] {
            dp[j] = true;
        } else {
            dp[j] = false;
        }
        j += 1;
    }

    let mut i: usize = 1;
    while i <= m {
        dp[0] = dp[0] && s1[i - 1] == s3[i - 1];

        j = 1;
        while j <= n {
            let old_from_s1 = dp[j];
            let from_s1 = old_from_s1 && s1[i - 1] == s3[i + j - 1];

            let current_left = dp[j - 1];
            let from_s2 = current_left && s2[j - 1] == s3[i + j - 1];

            dp[j] = from_s1 || from_s2;
            j += 1;
        }

        i += 1;
    }

    dp[n]
}
