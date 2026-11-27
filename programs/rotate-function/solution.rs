pub fn max_rotate_function(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n == 0 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut current: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        total += nums[i];
        current += (i as i64) * nums[i];
        i += 1;
    }

    let mut best: i64 = current;
    let mut k: usize = 1;

    while k < n {
        let idx: usize = n - k;
        current = current + total - (n as i64) * nums[idx];

        if current > best {
            best = current;
        }

        k += 1;
    }

    best
}
