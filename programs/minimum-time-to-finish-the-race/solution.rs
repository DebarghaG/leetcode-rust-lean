pub fn minimum_finish_time(tires: &[Vec<i64>], changeTime: i64, numLaps: i64) -> i64 {
    let n: usize = numLaps as usize;
    let inf: i64 = 1_000_000_000_000_000_000;

    // Smallest first-lap time among all tires (used to bound useful run lengths).
    let mut min_first: i64 = tires[0][0];
    let mut ti: usize = 1;
    while ti < tires.len() {
        let f = tires[ti][0];
        if f < min_first {
            min_first = f;
        }
        ti += 1;
    }

    // best[k] = minimum time to do k consecutive laps with a single tire,
    // without paying any change time.
    let mut best: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= n {
        best.push(inf);
        k += 1;
    }

    ti = 0;
    while ti < tires.len() {
        let f = tires[ti][0];
        let r = tires[ti][1];

        let mut cur = f;
        let mut sum = 0i64;
        let mut lap: usize = 1;

        while lap <= n {
            sum += cur;
            if sum < best[lap] {
                best[lap] = sum;
            }
            if lap == n {
                break;
            }
            let next = cur * r;
            // Beyond this point a fresh tire (changeTime + min_first) is cheaper.
            if next > changeTime + min_first {
                break;
            }
            cur = next;
            lap += 1;
        }
        ti += 1;
    }

    // dp[l] = minimum time to finish l laps overall.
    let mut dp: Vec<i64> = Vec::new();
    k = 0;
    while k <= n {
        dp.push(inf);
        k += 1;
    }
    dp[0] = 0;

    let mut laps: usize = 1;
    while laps <= n {
        let mut best_val = inf;
        let mut j: usize = 1;

        while j <= laps {
            let seg = best[j];
            if seg < inf / 2 {
                let prev = dp[laps - j];
                if prev < inf / 2 {
                    let rem = laps - j;
                    let extra: i64 = if rem > 0 { changeTime } else { 0 };
                    let cand = prev + seg + extra;
                    if cand < best_val {
                        best_val = cand;
                    }
                }
            }
            j += 1;
        }

        dp[laps] = best_val;
        laps += 1;
    }

    dp[n]
}
