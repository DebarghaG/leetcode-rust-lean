pub fn is_majority_element(nums: &[i64], target: i64) -> bool {
    let n = nums.len();
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < n {
        if nums[i] == target {
            count += 1;
        }
        i += 1;
    }

    count > n / 2
}
