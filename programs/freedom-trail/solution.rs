pub fn find_rotate_steps(ring: &[u8], key: &[u8]) -> i64 {
    let n = ring.len();
    let inf: i64 = 1000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut n_i: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if i == 0 {
            dp.push(0);
        } else {
            dp.push(inf);
        }
        n_i += 1;
        i += 1;
    }

    let mut k: usize = 0;
    while k < key.len() {
        let target = key[k];

        let mut ndp: Vec<i64> = Vec::new();
        let mut init: usize = 0;
        while init < n {
            ndp.push(inf);
            init += 1;
        }

        let mut j: usize = 0;
        let mut j_pos: i64 = 0;
        while j < n {
            if ring[j] == target {
                let mut best: i64 = inf;

                let mut p: usize = 0;
                let mut p_pos: i64 = 0;
                while p < n {
                    let mut diff: i64 = p_pos - j_pos;
                    if diff < 0 {
                        diff = -diff;
                    }

                    let mut dist: i64 = diff;
                    let other: i64 = n_i - diff;
                    if other < dist {
                        dist = other;
                    }

                    let candidate: i64 = dp[p] + dist + 1;
                    if candidate < best {
                        best = candidate;
                    }

                    p += 1;
                    p_pos += 1;
                }

                ndp[j] = best;
            }

            j += 1;
            j_pos += 1;
        }

        dp = ndp;
        k += 1;
    }

    let mut ans: i64 = inf;
    let mut i2: usize = 0;
    while i2 < n {
        if dp[i2] < ans {
            ans = dp[i2];
        }
        i2 += 1;
    }

    ans
}
