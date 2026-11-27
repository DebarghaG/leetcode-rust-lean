pub fn distribute_cookies(cookies: &[i64], k: i64) -> i64 {
    let n: usize = cookies.len();
    let kk: usize = k as usize;

    let mut size: usize = 1;
    let mut z: usize = 0;
    while z < n {
        size *= 2;
        z += 1;
    }

    let mut sums: Vec<i64> = Vec::new();
    let mut mask: usize = 0;
    while mask < size {
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if ((mask >> i) & 1) == 1 {
                s += cookies[i];
            }
            i += 1;
        }
        sums.push(s);
        mask += 1;
    }

    let inf: i64 = 1_000_000_000_000_000;
    let total_len: usize = (kk + 1) * size;

    let mut dp: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < total_len {
        dp.push(inf);
        idx += 1;
    }
    dp[0] = 0;

    let mut g: usize = 1;
    while g <= kk {
        let mut m: usize = 0;
        while m < size {
            let mut best: i64 = inf;
            let mut sub: usize = m;

            while sub > 0 {
                let prev = dp[(g - 1) * size + (m ^ sub)];
                let group_sum = sums[sub];

                let mut val = prev;
                if group_sum > val {
                    val = group_sum;
                }
                if val < best {
                    best = val;
                }

                sub = (sub - 1) & m;
            }

            dp[g * size + m] = best;
            m += 1;
        }
        g += 1;
    }

    dp[kk * size + (size - 1)]
}
