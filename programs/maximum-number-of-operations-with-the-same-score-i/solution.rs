pub fn max_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let target = nums[0] + nums[1];
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i + 1 < n {
        if nums[i] + nums[i + 1] == target {
            count += 1;
            i += 2;
        } else {
            break;
        }
    }

    count
}
