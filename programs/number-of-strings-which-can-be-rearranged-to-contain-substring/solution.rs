pub fn string_count(n: i64) -> i64 {
    let md: i64 = 1000000007;

    let mut dp: Vec<i64> = Vec::new();
    let mut ndp: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < 12 {
        dp.push(0);
        ndp.push(0);
        i += 1;
    }

    dp[0] = 1;

    let mut step: i64 = 0;
    while step < n {
        let mut r: usize = 0;
        while r < 12 {
            ndp[r] = 0;
            r += 1;
        }

        let mut s: usize = 0;
        while s < 12 {
            let val: i64 = dp[s];

            if val != 0 {
                let l: usize = s / 6;
                let e: usize = (s / 2) % 3;
                let t: usize = s % 2;

                // One of the 23 letters other than 'l', 'e', and 't'.
                ndp[s] = (ndp[s] + val * 23) % md;

                // Choose 'l'.
                let target_l: usize = 6 + e * 2 + t;
                ndp[target_l] = (ndp[target_l] + val) % md;

                // Choose 'e'.
                let mut ne: usize = e;
                if e < 2 {
                    ne = e + 1;
                } else {
                    ne = 2;
                }
                let target_e: usize = l * 6 + ne * 2 + t;
                ndp[target_e] = (ndp[target_e] + val) % md;

                // Choose 't'.
                let target_t: usize = l * 6 + e * 2 + 1;
                ndp[target_t] = (ndp[target_t] + val) % md;
            }

            s += 1;
        }

        let mut c: usize = 0;
        while c < 12 {
            dp[c] = ndp[c];
            c += 1;
        }

        step += 1;
    }

    dp[11]
}
