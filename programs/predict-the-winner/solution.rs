pub fn predict_the_winner(nums: &[i64]) -> bool {
    let n = nums.len();
    if n == 0 {
        return true;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        dp.push(nums[i]);
        i += 1;
    }

    let mut len = 2;
    while len <= n {
        let mut start = 0;
        while start + len <= n {
            let end = start + len - 1;
            let take_left = nums[start] - dp[start + 1];
            let take_right = nums[end] - dp[start];

            if take_left > take_right {
                dp[start] = take_left;
            } else {
                dp[start] = take_right;
            }

            start += 1;
        }
        len += 1;
    }

    dp[0] >= 0
}
