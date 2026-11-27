pub fn find_min(nums: &[i64]) -> i64 {
    let mut min_val = nums[0];
    let n = nums.len();
    let mut i: usize = 1;
    while i < n {
        if nums[i] < min_val {
            min_val = nums[i];
        }
        i += 1;
    }
    min_val
}
