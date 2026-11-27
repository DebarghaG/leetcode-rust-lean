pub fn count_alternating_subarrays(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut total: i64 = 1;
    let mut current: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if nums[i] == nums[i - 1] {
            current = 1;
        } else {
            current += 1;
        }
        total += current;
        i += 1;
    }

    total
}
