fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

pub fn self_divisible_permutation_count(n: i64) -> i64 {
    let n_usize = n as usize;
    let total = 1usize << n_usize;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        dp.push(0);
        i += 1;
    }
    dp[0] = 1;

    let mut mask: usize = 0;
    while mask < total {
        let ways = dp[mask];
        if ways != 0 {
            let mut k: usize = 0;
            let mut tmp = mask;
            while tmp > 0 {
                if (tmp & 1usize) == 1usize {
                    k += 1;
                }
                tmp = tmp >> 1;
            }

            let pos = k + 1;
            let mut idx: usize = 0;
            while idx < n_usize {
                let bit = 1usize << idx;
                if (mask & bit) == 0 {
                    let value = (idx + 1) as i64;
                    if gcd(value, pos as i64) == 1 {
                        let next = mask | bit;
                        dp[next] = dp[next] + ways;
                    }
                }
                idx += 1;
            }
        }
        mask += 1;
    }

    dp[total - 1]
}
