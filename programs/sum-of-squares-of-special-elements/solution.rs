pub fn sum_of_squares(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut total: i64 = 0;
    let mut i: usize = 1;

    while i <= n {
        if n % i == 0 {
            let x = nums[i - 1];
            total += x * x;
        }
        i += 1;
    }

    total
}
