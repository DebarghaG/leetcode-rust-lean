fn substring_cost(s: &[u8], l: usize, r: usize) -> i64 {
    let inf: i64 = 1000000000;
    let len = r - l + 1;

    if len <= 1 {
        return inf;
    }

    let mut best = inf;
    let mut d: usize = 1;

    while d < len {
        if len % d == 0 {
            let mut changes: i64 = 0;
            let mut q: usize = 0;

            while q < d {
                let group_len = (len - 1 - q) / d + 1;
                let mut p: usize = 0;

                while p < group_len / 2 {
                    let pos1 = l + q + p * d;
                    let pos2 = l + q + (group_len - 1 - p) * d;

                    if s[pos1] != s[pos2] {
                        changes += 1;
                    }

                    p += 1;
                }

                q += 1;
            }

            if changes < best {
                best = changes;
            }
        }

        d += 1;
    }

    best
}

pub fn minimum_changes(s: &[u8], k: i64) -> i64 {
    let inf: i64 = 1000000000;
    let n = s.len();

    let mut cost: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;

        while j < n {
            row.push(inf);
            j += 1;
        }

        cost.push(row);
        i += 1;
    }

    let mut l: usize = 0;

    while l < n {
        let mut r: usize = l + 1;

        while r < n {
            cost[l][r] = substring_cost(s, l, r);
            r += 1;
        }

        l += 1;
    }

    let kk = k as usize;
    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut p: usize = 0;

    while p <= kk {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;

        while j <= n {
            row.push(inf);
            j += 1;
        }

        dp.push(row);
        p += 1;
    }

    dp[0][0] = 0;

    let mut parts: usize = 1;

    while parts <= kk {
        let mut end: usize = 1;

        while end <= n {
            let mut start: usize = 0;

            while start < end {
                let prev = dp[parts - 1][start];
                let c = cost[start][end - 1];

                if prev < inf && c < inf {
                    let candidate = prev + c;

                    if candidate < dp[parts][end] {
                        dp[parts][end] = candidate;
                    }
                }

                start += 1;
            }

            end += 1;
        }

        parts += 1;
    }

    dp[kk][n]
}
