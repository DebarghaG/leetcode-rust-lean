pub fn maximum_top(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    if n == 0 {
        return -1;
    }

    if n == 1 {
        if k % 2 == 1 {
            return -1;
        }
        return nums[0];
    }

    let nm = n as i64;
    let mut ans: i64 = -1;

    // Elements that can be removed and then placed back as the final move.
    let mut limit: i64 = k - 1;
    if limit > nm {
        limit = nm;
    }

    if limit > 0 {
        let lim = limit as usize;
        let mut i: usize = 0;
        while i < lim {
            if nums[i] > ans {
                ans = nums[i];
            }
            i += 1;
        }
    }

    // If we only remove k times and the pile is still non-empty.
    if k >= 0 && k < nm {
        let idx = k as usize;
        if nums[idx] > ans {
            ans = nums[idx];
        }
    }

    ans
}
