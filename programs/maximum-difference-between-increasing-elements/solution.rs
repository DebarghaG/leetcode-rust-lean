pub fn maximum_difference(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 2 {
        return -1;
    }

    let mut min_val = nums[0];
    let mut best = -1;

    let mut i = 1;
    while i < n {
        if nums[i] > min_val {
            let diff = nums[i] - min_val;
            if diff > best {
                best = diff;
            }
        }
        if nums[i] < min_val {
            min_val = nums[i];
        }
        i += 1;
    }

    best
}
