pub fn is_monotonic(nums: &[i64]) -> bool {
    let n = nums.len();
    let mut increasing: bool = true;
    let mut decreasing: bool = true;

    let mut i: usize = 1;
    while i < n {
        if nums[i] < nums[i - 1] {
            increasing = false;
        }
        if nums[i] > nums[i - 1] {
            decreasing = false;
        }
        i += 1;
    }

    increasing || decreasing
}
