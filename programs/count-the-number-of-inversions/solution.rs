pub fn number_of_permutations(n: i64, requirements: &[Vec<i64>]) -> i64 {
    let modulo: i64 = 1000000007;
    let n_usize: usize = n as usize;

    let mut req: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        req.push(-1);
        i += 1;
    }

    let mut max_cnt: i64 = 0;
    i = 0;
    while i < requirements.len() {
        let row = &requirements[i];
        let end_i: i64 = row[0];
        let cnt_i: i64 = row[1];
        let end_u: usize = end_i as usize;

        if end_u < n_usize {
            req[end_u] = cnt_i;
        }
        if cnt_i > max_cnt {
            max_cnt = cnt_i;
        }

        i += 1;
    }

    if max_cnt < 0 {
        max_cnt = 0;
    }

    let width: usize = (max_cnt as usize) + 1;

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < width {
        dp.push(0);
        z += 1;
    }
    dp[0] = 1;

    let mut len: usize = 1;
    while len <= n_usize {
        let mut ndp: Vec<i64> = Vec::new();
        let mut z2: usize = 0;
        while z2 < width {
            ndp.push(0);
            z2 += 1;
        }

        let mut j: usize = 0;
        while j < width {
            let mut sum: i64 = 0;
            let mut d: usize = 0;

            while d < len {
                if d > j {
                    break;
                }
                sum += dp[j - d];
                sum %= modulo;
                d += 1;
            }

            ndp[j] = sum;
            j += 1;
        }

        let required = req[len - 1];
        if required != -1 {
            let c: usize = required as usize;
            let mut j2: usize = 0;
            while j2 < width {
                if j2 != c {
                    ndp[j2] = 0;
                }
                j2 += 1;
            }
        }

        dp = ndp;
        len += 1;
    }

    let final_required = req[n_usize - 1];
    if final_required < 0 {
        return 0;
    }

    dp[final_required as usize]
}
