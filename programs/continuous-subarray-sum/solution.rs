pub fn check_subarray_sum(nums: &[i64], k: i64) -> bool {
    let n = nums.len();
    if n < 2 {
        return false;
    }

    if k == 0 {
        let mut i: usize = 0;
        while i + 1 < n {
            if nums[i] == 0 && nums[i + 1] == 0 {
                return true;
            }
            i += 1;
        }
        return false;
    }

    let mut cap: usize = 1;
    while cap < (n + 1) * 2 {
        cap = cap * 2;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();

    let mut t: usize = 0;
    while t < cap {
        keys.push(-1);
        vals.push(-1);
        t += 1;
    }

    let mask: usize = cap - 1;

    // Prefix remainder 0 occurs before the array starts, at index -1.
    keys[0] = 0;
    vals[0] = -1;

    let mut prefix: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        prefix = (prefix + nums[i]) % k;
        let r = prefix;

        let mut pos: usize = (r as usize) & mask;
        while keys[pos] != -1 && keys[pos] != r {
            pos = (pos + 1) & mask;
        }

        if keys[pos] == r {
            let prev = vals[pos];
            let cur = i as i64;
            if cur - prev >= 2 {
                return true;
            }
        } else {
            keys[pos] = r;
            vals[pos] = i as i64;
        }

        i += 1;
    }

    false
}
