pub fn paint_walls(cost: &[i64], time: &[i64]) -> i64 {
    let n = cost.len();
    let inf: i64 = 1000000000000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        dp.push(inf);
        i += 1;
    }
    dp[0] = 0;

    let mut idx: usize = 0;
    while idx < n {
        let c = cost[idx];
        let t = time[idx];

        let mut j: i64 = n as i64;
        while j >= 0 {
            let ju: usize = j as usize;
            let cur = dp[ju];

            if cur < inf {
                let mut nj: i64 = j + t + 1;
                if nj > n as i64 {
                    nj = n as i64;
                }

                let nju: usize = nj as usize;
                let candidate = cur + c;
                if candidate < dp[nju] {
                    dp[nju] = candidate;
                }
            }

            j -= 1;
        }

        idx += 1;
    }

    dp[n]
}
