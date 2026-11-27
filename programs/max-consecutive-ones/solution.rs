pub fn find_max_consecutive_ones(nums: &[i64]) -> i64 {
    let mut max_count: i64 = 0;
    let mut current_count: i64 = 0;
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        if nums[i] == 1 {
            current_count += 1;
            if current_count > max_count {
                max_count = current_count;
            }
        } else {
            current_count = 0;
        }
        i += 1;
    }

    max_count
}
