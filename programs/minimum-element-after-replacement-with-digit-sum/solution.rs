pub fn min_element(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut min_sum: i64 = 1000000;
    let mut i: usize = 0;

    while i < n {
        let mut x: i64 = nums[i];
        let mut sum: i64 = 0;

        while x > 0 {
            sum += x % 10;
            x = x / 10;
        }

        if sum < min_sum {
            min_sum = sum;
        }

        i += 1;
    }

    min_sum
}
