pub fn min_array_length(nums: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();

    if n == 0 {
        return 0;
    }

    // With nonnegative nums, if k is negative no operation is possible.
    if k < 0 {
        return n as i64;
    }

    // If there is any zero, it can absorb every other element one by one.
    let mut z: usize = 0;
    while z < n {
        if nums[z] == 0 {
            return 1;
        }
        z += 1;
    }

    let mut ans: i64 = 0;
    let mut cur: i64 = 1;
    let mut has_current: bool = false;
    let mut i: usize = 0;

    while i < n {
        let v: i64 = nums[i];

        if !has_current {
            cur = v;
            has_current = true;

            // A value larger than k can never be merged with any positive value.
            if v > k {
                ans += 1;
                has_current = false;
                cur = 1;
            }

            i += 1;
        } else {
            // Since there are no zeros, all values are positive.
            if v <= k / cur {
                cur = cur * v;
                i += 1;
            } else {
                ans += 1;
                has_current = false;
                cur = 1;
            }
        }
    }

    if has_current {
        ans += 1;
    }

    ans
}
