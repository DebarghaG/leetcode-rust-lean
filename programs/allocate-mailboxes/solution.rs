pub fn min_distance(houses: &[i64], k: i64) -> i64 {
    let n: usize = houses.len();
    if n == 0 {
        return 0;
    }

    let n_i: i64 = n as i64;
    if k >= n_i {
        return 0;
    }

    let kk: usize = k as usize;

    let mut arr: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        arr.push(houses[i]);
        i += 1;
    }

    // Selection sort.
    i = 0;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            if arr[j] < arr[i] {
                let tmp: i64 = arr[i];
                arr[i] = arr[j];
                arr[j] = tmp;
            }
            j += 1;
        }
        i += 1;
    }

    // cost[i][j] = minimum distance to serve houses i..=j with one mailbox.
    let mut cost: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            row.push(0);
            j += 1;
        }
        cost.push(row);
        i += 1;
    }

    i = 0;
    while i < n {
        let mut j: usize = i;
        while j < n {
            let mid: usize = (i + j) / 2;
            let mut sum: i64 = 0;
            let mut t: usize = i;
            while t <= j {
                let mut diff: i64 = arr[t] - arr[mid];
                if diff < 0 {
                    diff = -diff;
                }
                sum += diff;
                t += 1;
            }
            cost[i][j] = sum;
            j += 1;
        }
        i += 1;
    }

    let inf: i64 = 1000000000000;

    // dp[g][i] = minimum cost to serve the first i houses with g mailboxes.
    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut g: usize = 0;
    while g <= kk {
        let mut row: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx <= n {
            row.push(inf);
            idx += 1;
        }
        dp.push(row);
        g += 1;
    }

    dp[0][0] = 0;

    g = 1;
    while g <= kk {
        let mut i2: usize = 1;
        while i2 <= n {
            let mut best: i64 = inf;
            let mut p: usize = 0;
            while p < i2 {
                let prev: i64 = dp[g - 1][p];
                if prev < inf {
                    let cand: i64 = prev + cost[p][i2 - 1];
                    if cand < best {
                        best = cand;
                    }
                }
                p += 1;
            }
            dp[g][i2] = best;
            i2 += 1;
        }
        g += 1;
    }

    dp[kk][n]
}
