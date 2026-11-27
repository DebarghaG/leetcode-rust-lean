fn encoded_run_cost(cnt: usize) -> i64 {
    if cnt == 0usize {
        return 0i64;
    }
    if cnt == 1usize {
        return 1i64;
    }
    if cnt < 10usize {
        return 2i64;
    }
    if cnt < 100usize {
        return 3i64;
    }
    4i64
}

pub fn get_length_of_optimal_compression(s: &[u8], k: i64) -> i64 {
    let n = s.len();

    let mut kk = 0usize;
    if k > 0i64 {
        let ku = k as usize;
        if ku > n {
            kk = n;
        } else {
            kk = ku;
        }
    }

    let cols = kk + 1usize;
    let size = (n + 1usize) * cols;
    let inf = 1000000000i64;

    let mut dp: Vec<i64> = Vec::new();
    let mut z = 0usize;
    while z < size {
        dp.push(inf);
        z += 1usize;
    }

    let mut j0 = 0usize;
    while j0 < cols {
        dp[j0] = 0i64;
        j0 += 1usize;
    }

    let mut i = 1usize;
    while i <= n {
        let target = s[i - 1usize] as usize;

        let mut j = 0usize;
        while j < cols {
            let mut best = inf;

            if j > 0usize {
                let del_candidate = dp[(i - 1usize) * cols + (j - 1usize)];
                if del_candidate < best {
                    best = del_candidate;
                }
            }

            let mut same = 0usize;
            let mut diff = 0usize;
            let mut p = i;

            while p > 0usize {
                p -= 1usize;

                if s[p] as usize == target {
                    same += 1usize;
                } else {
                    diff += 1usize;
                }

                if diff <= j {
                    let prev = dp[p * cols + (j - diff)];
                    if prev < inf {
                        let cost = encoded_run_cost(same);
                        let candidate = prev + cost;
                        if candidate < best {
                            best = candidate;
                        }
                    }
                }
            }

            dp[i * cols + j] = best;
            j += 1usize;
        }

        i += 1usize;
    }

    dp[n * cols + kk]
}
