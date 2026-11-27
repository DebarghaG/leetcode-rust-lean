fn abs_diff(a: i64, b: i64) -> i64 {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

fn bit_at(k: usize) -> usize {
    let mut r: usize = 1;
    let mut i: usize = 0;
    while i < k {
        r = r * 2;
        i += 1;
    }
    r
}

pub fn find_permutation(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    if n == 0 {
        let empty: Vec<i64> = Vec::new();
        return empty;
    }

    let total = bit_at(n);
    let full = total - 1;
    let inf: i64 = 1000000000;

    let dp_len = total * n;
    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < dp_len {
        dp.push(inf);
        i += 1;
    }

    let mut last: usize = 0;
    while last < n {
        dp[full * n + last] = abs_diff(last as i64, nums[0]);
        last += 1;
    }

    let mut mask: usize = full;
    while mask > 0 {
        mask = mask - 1;

        let mut last_idx: usize = 0;
        while last_idx < n {
            let last_bit = bit_at(last_idx);
            if (mask & last_bit) != 0 {
                let mut best = inf;

                let mut v: usize = 0;
                while v < n {
                    let v_bit = bit_at(v);
                    if (mask & v_bit) == 0 {
                        let edge = abs_diff(last_idx as i64, nums[v]);
                        let next_mask = mask | v_bit;
                        let tail = dp[next_mask * n + v];
                        let candidate = edge + tail;
                        if candidate < best {
                            best = candidate;
                        }
                    }
                    v += 1;
                }

                if best < inf {
                    dp[mask * n + last_idx] = best;
                }
            }

            last_idx += 1;
        }
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(0);

    let mut used: usize = bit_at(0);
    let mut cur: usize = 0;
    let mut pos: usize = 1;

    while pos < n {
        let mut chosen: usize = n;
        let mut v: usize = 0;

        while v < n {
            let v_bit = bit_at(v);
            if (used & v_bit) == 0 {
                let edge = abs_diff(cur as i64, nums[v]);
                let next_mask = used | v_bit;
                let tail = dp[next_mask * n + v];
                let candidate = edge + tail;
                let current_best = dp[used * n + cur];

                if candidate == current_best {
                    chosen = v;
                    break;
                }
            }
            v += 1;
        }

        result.push(chosen as i64);
        used = used | bit_at(chosen);
        cur = chosen;
        pos += 1;
    }

    result
}
