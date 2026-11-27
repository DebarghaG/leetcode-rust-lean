pub fn minimize_array_value(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut sum: i64 = 0;
    let mut len: i64 = 0;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        sum += nums[i];
        len += 1;

        let value = (sum + len - 1) / len;
        if value > ans {
            ans = value;
        }

        i += 1;
    }

    ans
}
