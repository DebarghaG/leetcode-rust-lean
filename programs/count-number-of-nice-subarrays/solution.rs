fn at_most(nums: &[i64], k: i64) -> i64 {
    if k < 0 {
        return 0;
    }

    let n = nums.len();
    let mut ans: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut odds: i64 = 0;

    while right < n {
        if nums[right] % 2 != 0 {
            odds += 1;
        }

        while odds > k {
            if nums[left] % 2 != 0 {
                odds -= 1;
            }
            left += 1;
        }

        if left <= right {
            ans += (right - left + 1) as i64;
        }
        right += 1;
    }

    ans
}

pub fn number_of_subarrays(nums: &[i64], k: i64) -> i64 {
    at_most(nums, k) - at_most(nums, k - 1)
}
