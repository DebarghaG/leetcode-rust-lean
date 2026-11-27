pub fn return_to_boundary_count(nums: &[i64]) -> i64 {
    let mut position: i64 = 0;
    let mut count: i64 = 0;
    let n = nums.len();

    for i in 0..n {
        position += nums[i];
        if position == 0 {
            count += 1;
        }
    }

    count
}
