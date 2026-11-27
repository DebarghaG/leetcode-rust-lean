pub fn min_difficulty(jobDifficulty: &[i64], d: i64) -> i64 {
    let n: usize = jobDifficulty.len();

    if d <= 0 {
        return -1;
    }

    let mut days: usize = 0;
    let mut t: i64 = 0;
    while t < d {
        days += 1;
        t += 1;
    }

    if days > n {
        return -1;
    }

    let inf: i64 = 1_000_000_000;

    let mut prev: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        prev.push(inf);
        i += 1;
    }

    prev[0] = 0;

    let mut running: i64 = 0;
    i = 0;
    while i < n {
        if jobDifficulty[i] > running {
            running = jobDifficulty[i];
        }
        prev[i + 1] = running;
        i += 1;
    }

    let mut day: usize = 2;
    while day <= days {
        let mut cur: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z <= n {
            cur.push(inf);
            z += 1;
        }

        let day_minus_1: usize = day - 1;

        let mut j: usize = day;
        while j <= n {
            let mut best: i64 = inf;
            let mut cur_max: i64 = 0;
            let mut k: usize = j;

            while k > day_minus_1 {
                k -= 1;
                if jobDifficulty[k] > cur_max {
                    cur_max = jobDifficulty[k];
                }

                let prev_val: i64 = prev[k];
                if prev_val < inf {
                    let candidate: i64 = prev_val + cur_max;
                    if candidate < best {
                        best = candidate;
                    }
                }
            }

            cur[j] = best;
            j += 1;
        }

        prev = cur;
        day += 1;
    }

    if prev[n] >= inf {
        -1
    } else {
        prev[n]
    }
}
