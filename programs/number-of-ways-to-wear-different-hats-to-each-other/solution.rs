pub fn number_ways(hats: &[Vec<i64>]) -> i64 {
    let modulo: i64 = 1000000007;
    let n: usize = hats.len();
    let total: usize = 1usize << n;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        dp.push(0);
        i += 1;
    }
    dp[0] = 1;

    let mut max_hat: i64 = 0;
    let mut a: usize = 0;
    while a < n {
        let prefs = &hats[a];
        let mut b: usize = 0;
        while b < prefs.len() {
            if prefs[b] > max_hat {
                max_hat = prefs[b];
            }
            b += 1;
        }
        a += 1;
    }

    let mut hat: i64 = 1;
    while hat <= max_hat {
        let mut next: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z < total {
            next.push(dp[z]);
            z += 1;
        }

        let mut mask: usize = 0;
        while mask < total {
            let cur: i64 = dp[mask];
            if cur != 0 {
                let mut p: usize = 0;
                while p < n {
                    let bit: usize = 1usize << p;
                    if (mask & bit) == 0 {
                        let prefs = &hats[p];
                        let mut likes: bool = false;
                        let mut j: usize = 0;
                        while j < prefs.len() {
                            if prefs[j] == hat {
                                likes = true;
                            }
                            j += 1;
                        }

                        if likes {
                            let new_mask: usize = mask | bit;
                            let mut value: i64 = next[new_mask] + cur;
                            if value >= modulo {
                                value -= modulo;
                            }
                            next[new_mask] = value;
                        }
                    }
                    p += 1;
                }
            }
            mask += 1;
        }

        dp = next;
        hat += 1;
    }

    dp[total - 1]
}
