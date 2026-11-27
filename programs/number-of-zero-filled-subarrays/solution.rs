pub fn zero_filled_subarray(nums: &[i64]) -> i64 {
    let mut total: i64 = 0;
    let mut run: i64 = 0;
    let n: usize = nums.len();
    let mut i: usize = 0;

    while i < n {
        if nums[i] == 0 {
            run += 1;
            total += run;
        } else {
            run = 0;
        }
        i += 1;
    }

    total
}
