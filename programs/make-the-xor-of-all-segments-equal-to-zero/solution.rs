pub fn min_changes(nums: &[i64], k: i64) -> i64 {
    const M: usize = 1024;
    const INF: i64 = 1_000_000_000;

    let n = nums.len();
    let kk = k as usize;

    let mut dp: Vec<i64> = Vec::new();
    dp.push(0);
    let mut i: usize = 1;
    while i < M {
        dp.push(INF);
        i += 1;
    }

    let mut r: usize = 0;
    while r < kk {
        let mut freq: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < M {
            freq.push(0);
            j += 1;
        }

        let mut sz: i64 = 0;
        let mut pos: usize = r;
        while pos < n {
            let idx = nums[pos] as usize;
            if idx < M {
                freq[idx] += 1;
            }
            sz += 1;
            pos += kk;
        }

        let mut min_dp: i64 = INF;
        j = 0;
        while j < M {
            if dp[j] < min_dp {
                min_dp = dp[j];
            }
            j += 1;
        }

        let mut ndp: Vec<i64> = Vec::new();
        j = 0;
        while j < M {
            ndp.push(min_dp + sz);
            j += 1;
        }

        j = 0;
        while j < M {
            if freq[j] > 0 {
                let v = j;
                let f = freq[j];
                let mut s: usize = 0;
                while s < M {
                    let target = s ^ v;
                    let cost = dp[s] + sz - f;
                    if cost < ndp[target] {
                        ndp[target] = cost;
                    }
                    s += 1;
                }
            }
            j += 1;
        }

        dp = ndp;
        r += 1;
    }

    dp[0]
}
