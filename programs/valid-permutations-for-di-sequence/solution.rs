pub fn num_perms_di_sequence(s: &[u8]) -> i64 {
    const MOD: i64 = 1000000007;

    let n: usize = s.len();
    let mut dp: Vec<i64> = Vec::new();
    dp.push(1);

    let mut i: usize = 0;
    while i < n {
        let len: usize = dp.len();
        let mut next: Vec<i64> = Vec::new();

        if s[i] == b'I' {
            let mut running: i64 = 0;
            let mut j: usize = 0;
            while j < len + 1 {
                next.push(running);
                if j < len {
                    running = (running + dp[j]) % MOD;
                }
                j += 1;
            }
        } else {
            let mut total: i64 = 0;
            let mut k: usize = 0;
            while k < len {
                total = (total + dp[k]) % MOD;
                k += 1;
            }

            let mut prefix: i64 = 0;
            let mut j: usize = 0;
            while j < len + 1 {
                let mut val: i64 = total - prefix;
                if val < 0 {
                    val += MOD;
                }
                next.push(val);

                if j < len {
                    prefix = (prefix + dp[j]) % MOD;
                }
                j += 1;
            }
        }

        dp = next;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut j: usize = 0;
    while j < dp.len() {
        ans = (ans + dp[j]) % MOD;
        j += 1;
    }

    ans
}
