pub fn find_middle_index(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    let mut left: i64 = 0;
    i = 0;
    while i < n {
        let right: i64 = total - left - nums[i];
        if left == right {
            return i as i64;
        }
        left += nums[i];
        i += 1;
    }

    -1
}
