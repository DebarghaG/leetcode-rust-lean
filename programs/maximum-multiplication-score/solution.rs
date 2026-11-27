pub fn max_score(a: &[i64], b: &[i64]) -> i64 {
    let neg: i64 = -1000000000000000000;

    let mut dp: Vec<i64> = Vec::new();
    dp.push(0);

    let mut k: usize = 1;
    while k < 5 {
        dp.push(neg);
        k = k + 1;
    }

    let mut i: usize = 0;
    while i < b.len() {
        let x = b[i];

        let mut kk: usize = 4;
        while kk >= 1 {
            let cand = dp[kk - 1] + a[kk - 1] * x;
            if cand > dp[kk] {
                dp[kk] = cand;
            }
            kk = kk - 1;
        }

        i = i + 1;
    }

    dp[4]
}
