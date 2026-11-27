pub fn longest_common_subsequence(text1: &[u8], text2: &[u8]) -> i64 {
    let n = text1.len();
    let m = text2.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut k = 0;
    while k <= m {
        dp.push(0);
        k += 1;
    }

    let mut i = 1;
    while i <= n {
        let mut diag = 0;
        let mut j = 1;
        while j <= m {
            let up = dp[j];

            if text1[i - 1] == text2[j - 1] {
                dp[j] = diag + 1;
            } else {
                let left = dp[j - 1];
                if left > up {
                    dp[j] = left;
                } else {
                    dp[j] = up;
                }
            }

            diag = up;
            j += 1;
        }
        i += 1;
    }

    dp[m]
}
