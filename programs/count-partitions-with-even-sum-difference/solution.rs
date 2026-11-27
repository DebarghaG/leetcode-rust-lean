pub fn count_partitions(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    if total % 2 == 0 {
        n as i64 - 1
    } else {
        0
    }
}
