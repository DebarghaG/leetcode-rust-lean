pub fn max_product(nums: &[i64]) -> i64 {
    let mut max1: i64 = 0;
    let mut max2: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        let x = nums[i];
        if x > max1 {
            max2 = max1;
            max1 = x;
        } else if x > max2 {
            max2 = x;
        }
        i += 1;
    }

    (max1 - 1) * (max2 - 1)
}
