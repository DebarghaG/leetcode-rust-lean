pub fn max_sum_after_partitioning(arr: &[i64], k: i64) -> i64 {
    let n: usize = arr.len();
    let mut dp: Vec<i64> = Vec::new();

    let mut z: usize = 0;
    while z <= n {
        dp.push(0);
        z += 1;
    }

    let ku: usize = k as usize;
    let mut i: usize = 1;
    while i <= n {
        let mut best: i64 = 0;
        let mut cur_max: i64 = 0;
        let mut j: usize = 1;

        while j <= i && j <= ku {
            let idx: usize = i - j;
            let v: i64 = arr[idx];
            if v > cur_max {
                cur_max = v;
            }

            let cand: i64 = dp[idx] + cur_max * (j as i64);
            if cand > best {
                best = cand;
            }

            j += 1;
        }

        dp[i] = best;
        i += 1;
    }

    dp[n]
}
