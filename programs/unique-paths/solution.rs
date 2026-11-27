pub fn unique_paths(m: i64, n: i64) -> i64 {
    if m <= 0 || n <= 0 {
        return 0;
    }

    let rows: usize = m as usize;
    let cols: usize = n as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < cols {
        dp.push(1);
        j += 1;
    }

    let mut i: usize = 1;
    while i < rows {
        let mut j: usize = 1;
        while j < cols {
            let from_left: i64 = dp[j - 1];
            let current: i64 = dp[j];
            dp[j] = current + from_left;
            j += 1;
        }
        i += 1;
    }

    dp[cols - 1]
}
