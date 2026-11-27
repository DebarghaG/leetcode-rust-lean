pub fn sum_of_digits(nums: &[i64]) -> i64 {
    let mut min = nums[0];
    let mut i = 1;
    while i < nums.len() {
        if nums[i] < min {
            min = nums[i];
        }
        i += 1;
    }

    let mut sum = 0;
    let mut x = min;
    while x > 0 {
        sum += x % 10;
        x = x / 10;
    }

    if sum % 2 == 0 {
        1
    } else {
        0
    }
}
