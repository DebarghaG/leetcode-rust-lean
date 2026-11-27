pub fn min_operations(nums: &[i64], k: i64) -> i64 {
    let mut count: i64 = 0;
    let mut i: usize = 0;
    let n: usize = nums.len();

    while i < n {
        if nums[i] < k {
            count += 1;
        }
        i += 1;
    }

    count
}
