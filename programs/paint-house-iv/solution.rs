pub fn min_cost(n: i64, cost: &[Vec<i64>]) -> i64 {
    let _ = n;
    let total_houses: usize = cost.len();
    let m: usize = total_houses / 2;
    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 9 {
        dp.push(inf);
        k += 1;
    }

    let mut c: usize = 0;
    while c < 3 {
        let mut d: usize = 0;
        while d < 3 {
            if c != d {
                dp[c * 3 + d] = cost[0][c] + cost[total_houses - 1][d];
            }
            d += 1;
        }
        c += 1;
    }

    let mut i: usize = 1;
    while i < m {
        let mut next_dp: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < 9 {
            next_dp.push(inf);
            k += 1;
        }

        let mut prev_c: usize = 0;
        while prev_c < 3 {
            let mut prev_d: usize = 0;
            while prev_d < 3 {
                let prev_val: i64 = dp[prev_c * 3 + prev_d];
                if prev_val < inf {
                    let mut cur_c: usize = 0;
                    while cur_c < 3 {
                        let mut cur_d: usize = 0;
                        while cur_d < 3 {
                            if cur_c != cur_d && cur_c != prev_c && cur_d != prev_d {
                                let candidate: i64 = prev_val
                                    + cost[i][cur_c]
                                    + cost[total_houses - 1 - i][cur_d];
                                let idx: usize = cur_c * 3 + cur_d;
                                if candidate < next_dp[idx] {
                                    next_dp[idx] = candidate;
                                }
                            }
                            cur_d += 1;
                        }
                        cur_c += 1;
                    }
                }
                prev_d += 1;
            }
            prev_c += 1;
        }

        dp = next_dp;
        i += 1;
    }

    let mut ans: i64 = inf;
    let mut s: usize = 0;
    while s < 9 {
        if dp[s] < ans {
            ans = dp[s];
        }
        s += 1;
    }

    ans
}
