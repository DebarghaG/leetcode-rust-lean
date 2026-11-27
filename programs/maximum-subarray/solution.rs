pub fn max_sub_array(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = nums[0];
    let mut current: i64 = nums[0];

    let mut i: usize = 1;
    while i < n {
        let x = nums[i];
        if current < 0 {
            current = x;
        } else {
            current = current + x;
        }

        if current > best {
            best = current;
        }

        i += 1;
    }

    best
}
