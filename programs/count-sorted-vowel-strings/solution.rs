pub fn count_vowel_strings(n: i64) -> i64 {
    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 5 {
        dp.push(1);
        i += 1;
    }

    let mut length: i64 = 1;
    while length < n {
        let mut j: usize = 1;
        while j < 5 {
            dp[j] = dp[j] + dp[j - 1];
            j += 1;
        }
        length += 1;
    }

    let mut total: i64 = 0;
    let mut k: usize = 0;
    while k < 5 {
        total += dp[k];
        k += 1;
    }

    total
}
