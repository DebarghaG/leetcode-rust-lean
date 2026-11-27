pub fn partition_disjoint(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut max_left: i64 = nums[0];
    let mut max_right: i64 = nums[0];
    let mut left_size: i64 = 1;

    let mut i: usize = 1;
    while i < n {
        let x = nums[i];

        if x < max_left {
            left_size = i as i64 + 1;
            max_left = max_right;
        }

        if x > max_right {
            max_right = x;
        }

        i += 1;
    }

    left_size
}
