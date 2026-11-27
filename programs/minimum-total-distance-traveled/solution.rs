pub fn minimum_total_distance(robot: &[i64], factory: &[Vec<i64>]) -> i64 {
    let n = robot.len();
    let m = factory.len();

    let mut robots: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        robots.push(robot[i]);
        i += 1;
    }

    i = 1;
    while i < n {
        let key = robots[i];
        let mut j = i;
        while j > 0 && robots[j - 1] > key {
            robots[j] = robots[j - 1];
            j -= 1;
        }
        robots[j] = key;
        i += 1;
    }

    let mut positions: Vec<i64> = Vec::new();
    let mut limits: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        positions.push(factory[i][0]);
        limits.push(factory[i][1]);
        i += 1;
    }

    i = 1;
    while i < m {
        let key_pos = positions[i];
        let key_lim = limits[i];
        let mut j = i;
        while j > 0 && positions[j - 1] > key_pos {
            positions[j] = positions[j - 1];
            limits[j] = limits[j - 1];
            j -= 1;
        }
        positions[j] = key_pos;
        limits[j] = key_lim;
        i += 1;
    }

    let inf: i64 = 1_000_000_000_000_000_000;
    let cols = m + 1;
    let total = (n + 1) * cols;

    let mut dp: Vec<i64> = Vec::new();
    let mut t = 0;
    while t < total {
        dp.push(inf);
        t += 1;
    }

    let mut j0 = 0;
    while j0 <= m {
        dp[j0] = 0;
        j0 += 1;
    }

    let mut fj = 1;
    while fj <= m {
        let pos = positions[fj - 1];
        let limit = limits[fj - 1];

        let mut i = 0;
        while i <= n {
            let mut best = dp[i * cols + (fj - 1)];
            let mut add: i64 = 0;
            let mut remaining: i64 = limit;
            let mut k: usize = 1;

            while k <= i && remaining > 0 {
                let idx = i - k;
                let diff = robots[idx] - pos;
                let dist = if diff < 0 { -diff } else { diff };
                add += dist;

                let prev = dp[idx * cols + (fj - 1)];
                if prev < inf {
                    let candidate = prev + add;
                    if candidate < best {
                        best = candidate;
                    }
                }

                remaining -= 1;
                k += 1;
            }

            dp[i * cols + fj] = best;
            i += 1;
        }

        fj += 1;
    }

    dp[n * cols + m]
}
