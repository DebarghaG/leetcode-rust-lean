pub fn average_value(nums: &[i64]) -> i64 {
    let mut sum: i64 = 0;
    let mut count: i64 = 0;

    let mut i: usize = 0;
    while i < nums.len() {
        let x = nums[i];
        if x % 2 == 0 && x % 3 == 0 {
            sum += x;
            count += 1;
        }
        i += 1;
    }

    if count == 0 {
        0
    } else {
        sum / count
    }
}
