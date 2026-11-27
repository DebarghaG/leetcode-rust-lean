pub fn min_size_subarray(nums: &[i64], target: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return -1;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    if total <= 0 {
        return -1;
    }

    let q: i64 = target / total;
    let rem: i64 = target % total;

    if rem == 0 {
        return q * (n as i64);
    }

    let mut doubled: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        doubled.push(nums[i]);
        i += 1;
    }
    i = 0;
    while i < n {
        doubled.push(nums[i]);
        i += 1;
    }

    let m = doubled.len();
    let mut best: i64 = -1;
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut s: i64 = 0;

    while right < m {
        s += doubled[right];

        while s > rem && left <= right {
            s -= doubled[left];
            left += 1;
        }

        if s == rem {
            let len = (right - left + 1) as i64;
            if best == -1 || len < best {
                best = len;
            }
        }

        right += 1;
    }

    if best == -1 {
        -1
    } else {
        q * (n as i64) + best
    }
}
