pub fn max_adjacent_distance(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i + 1 < n {
        let mut diff = nums[i] - nums[i + 1];
        if diff < 0 {
            diff = -diff;
        }
        if diff > best {
            best = diff;
        }
        i += 1;
    }

    let mut circular_diff = nums[0] - nums[n - 1];
    if circular_diff < 0 {
        circular_diff = -circular_diff;
    }
    if circular_diff > best {
        best = circular_diff;
    }

    best
}
