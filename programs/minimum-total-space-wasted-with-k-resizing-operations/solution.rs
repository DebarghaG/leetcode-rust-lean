pub fn min_space_wasted_k_resizing(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut gmax_i64 = k + 1;
    if gmax_i64 > n as i64 {
        gmax_i64 = n as i64;
    }
    let gmax = gmax_i64 as usize;

    let mut cost: Vec<Vec<i64>> = Vec::new();
    let mut l = 0;
    while l < n {
        let mut row: Vec<i64> = Vec::new();
        let mut z = 0;
        while z < n {
            row.push(0);
            z += 1;
        }

        let mut maxv: i64 = 0;
        let mut sum: i64 = 0;
        let mut r = l;
        while r < n {
            let x = nums[r];
            if x > maxv {
                maxv = x;
            }
            sum += x;

            let length = (r - l + 1) as i64;
            row[r] = maxv * length - sum;
            r += 1;
        }

        cost.push(row);
        l += 1;
    }

    let inf: i64 = 1000000000000000000;
    let mut dp: Vec<Vec<i64>> = Vec::new();

    let mut g = 0;
    while g <= gmax {
        let mut row: Vec<i64> = Vec::new();
        let mut i = 0;
        while i <= n {
            row.push(inf);
            i += 1;
        }
        dp.push(row);
        g += 1;
    }

    dp[0][0] = 0;

    g = 1;
    while g <= gmax {
        let mut i = g;
        while i <= n {
            let mut best = inf;
            let mut p = g - 1;

            while p < i {
                let prev = dp[g - 1][p];
                if prev != inf {
                    let candidate = prev + cost[p][i - 1];
                    if candidate < best {
                        best = candidate;
                    }
                }
                p += 1;
            }

            dp[g][i] = best;
            i += 1;
        }
        g += 1;
    }

    dp[gmax][n]
}
