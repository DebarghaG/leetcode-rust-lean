pub fn num_trees(n: i64) -> i64 {
    if n <= 0 {
        return 1;
    }

    let m: usize = n as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx <= m {
        dp.push(0);
        idx += 1;
    }

    dp[0] = 1;

    let mut len: usize = 1;
    while len <= m {
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        let mut j: usize = len;

        while i < len {
            j -= 1;
            sum += dp[i] * dp[j];
            i += 1;
        }

        dp[len] = sum;
        len += 1;
    }

    dp[m]
}
