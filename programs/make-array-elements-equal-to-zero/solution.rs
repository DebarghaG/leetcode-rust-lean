pub fn count_valid_selections(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut left: i64 = 0;

    i = 0;
    while i < n {
        if nums[i] == 0 {
            let right: i64 = total - left;
            let diff: i64 = if left > right { left - right } else { right - left };

            if diff == 0 {
                ans += 2;
            } else if diff == 1 {
                ans += 1;
            }
        }

        left += nums[i];
        i += 1;
    }

    ans
}
