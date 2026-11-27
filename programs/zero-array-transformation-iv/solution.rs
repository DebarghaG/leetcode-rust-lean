fn can_make_zero(nums: &[i64], queries: &[Vec<i64>], k: usize) -> bool {
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        let target_i64 = nums[i];
        if target_i64 < 0 {
            return false;
        }

        let target = target_i64 as usize;
        let mut dp: Vec<bool> = Vec::new();
        let mut t: usize = 0;
        while t <= target {
            dp.push(false);
            t += 1;
        }
        dp[0] = true;

        let mut j: usize = 0;
        while j < k {
            let row = &queries[j];
            let l = row[0];
            let r = row[1];
            let val = row[2];
            let pos = i as i64;

            if l <= pos && pos <= r && val > 0 {
                let v = val as usize;
                if v <= target {
                    let mut s: usize = target + 1;
                    while s > v {
                        s -= 1;
                        if dp[s - v] {
                            dp[s] = true;
                        }
                    }
                }
            }

            j += 1;
        }

        if !dp[target] {
            return false;
        }

        i += 1;
    }

    true
}

pub fn min_zero_array(nums: &[i64], queries: &[Vec<i64>]) -> i64 {
    let m = queries.len();

    if !can_make_zero(nums, queries, m) {
        return -1;
    }

    let mut lo: usize = 0;
    let mut hi: usize = m;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if can_make_zero(nums, queries, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo as i64
}
