pub fn minimum_cost(target: &[u8], words: &[Vec<u8>], costs: &[i64]) -> i64 {
    let n = target.len();
    let m = words.len();
    let inf: i64 = 1_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        dp.push(inf);
        i += 1;
    }
    dp[0] = 0;

    let mut pos: usize = 0;
    while pos < n {
        if dp[pos] != inf {
            let mut wi: usize = 0;
            while wi < m {
                let w = &words[wi];
                let wl = w.len();

                if pos + wl <= n {
                    let mut ok: bool = true;
                    let mut j: usize = 0;
                    while j < wl {
                        if ok {
                            if target[pos + j] != w[j] {
                                ok = false;
                            }
                        }
                        j += 1;
                    }

                    if ok {
                        let new_cost = dp[pos] + costs[wi];
                        if new_cost < dp[pos + wl] {
                            dp[pos + wl] = new_cost;
                        }
                    }
                }

                wi += 1;
            }
        }
        pos += 1;
    }

    if dp[n] == inf {
        -1
    } else {
        dp[n]
    }
}
