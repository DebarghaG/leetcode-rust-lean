pub fn first_missing_positive(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 1;
    }

    // seen[i] is true iff (i + 1) is present in nums.
    let mut seen: Vec<bool> = Vec::new();
    let mut i = 0usize;
    while i < n {
        seen.push(false);
        i += 1;
    }

    i = 0;
    while i < n {
        let v = nums[i];
        if v > 0 && v <= n as i64 {
            let idx = (v - 1) as usize;
            seen[idx] = true;
        }
        i += 1;
    }

    i = 0;
    while i < n {
        if !seen[i] {
            return (i + 1) as i64;
        }
        i += 1;
    }

    n as i64 + 1
}
