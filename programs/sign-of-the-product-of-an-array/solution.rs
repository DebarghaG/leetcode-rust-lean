pub fn array_sign(nums: &[i64]) -> i64 {
    let mut sign: i64 = 1;
    let mut i: usize = 0;
    let n: usize = nums.len();

    while i < n {
        let x: i64 = nums[i];
        if x == 0 {
            return 0;
        }
        if x < 0 {
            sign = -sign;
        }
        i = i + 1;
    }

    sign
}
