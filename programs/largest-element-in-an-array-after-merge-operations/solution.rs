pub fn max_array_value(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut cur: i64 = nums[n - 1];
    let mut i: usize = n - 1;

    while i > 0 {
        i -= 1;
        let x = nums[i];
        if cur >= x {
            cur += x;
        } else {
            cur = x;
        }
    }

    cur
}
