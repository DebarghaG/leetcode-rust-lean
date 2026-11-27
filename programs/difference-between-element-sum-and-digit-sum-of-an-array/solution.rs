pub fn difference_of_sum(nums: &[i64]) -> i64 {
    let mut element_sum: i64 = 0;
    let mut digit_sum: i64 = 0;

    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        let mut x = nums[i];
        element_sum += x;

        while x > 0 {
            digit_sum += x % 10;
            x = x / 10;
        }

        i += 1;
    }

    let mut diff = element_sum - digit_sum;
    if diff < 0 {
        diff = -diff;
    }

    diff
}
