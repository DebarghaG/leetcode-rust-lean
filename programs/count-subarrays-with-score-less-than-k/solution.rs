pub fn count_subarrays(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut sum: i64 = 0;
    let mut len: i64 = 0;

    while right < n {
        sum = sum + nums[right];
        len = len + 1;

        while len > 0 && sum * len >= k {
            sum = sum - nums[left];
            left = left + 1;
            len = len - 1;
        }

        ans = ans + len;
        right = right + 1;
    }

    ans
}
