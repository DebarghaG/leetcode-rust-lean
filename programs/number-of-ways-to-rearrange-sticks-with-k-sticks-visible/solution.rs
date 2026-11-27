pub fn rearrange_sticks(n: i64, k: i64) -> i64 {
    let md: i64 = 1000000007;

    if k <= 0 {
        if n == 0 && k == 0 {
            return 1;
        }
        return 0;
    }

    if n <= 0 || k > n {
        return 0;
    }

    let kk: usize = k as usize;
    let nn: usize = n as usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t <= kk {
        dp.push(0);
        t += 1;
    }
    dp[0] = 1;

    let mut i: usize = 1;
    while i <= nn {
        let mut j: usize = kk;
        while j > 0 {
            let prev = dp[j - 1];
            let old = dp[j];
            let term = (old * ((i - 1) as i64)) % md;

            let mut val = prev + term;
            if val >= md {
                val -= md;
            }
            dp[j] = val;

            j -= 1;
        }
        dp[0] = 0;
        i += 1;
    }

    dp[kk]
}
