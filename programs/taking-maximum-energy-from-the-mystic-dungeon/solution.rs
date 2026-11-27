pub fn maximum_energy(energy: &[i64], k: i64) -> i64 {
    let n = energy.len();
    if n == 0 {
        return 0;
    }

    let kk: usize = k as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut init = 0;
    while init < n {
        dp.push(0);
        init += 1;
    }

    let mut i = n;
    while i > 0 {
        i -= 1;

        let remaining = n - i;
        if kk < remaining {
            dp[i] = energy[i] + dp[i + kk];
        } else {
            dp[i] = energy[i];
        }
    }

    let mut best = dp[0];
    let mut j = 1;
    while j < n {
        if dp[j] > best {
            best = dp[j];
        }
        j += 1;
    }

    best
}
