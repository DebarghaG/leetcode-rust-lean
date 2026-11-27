fn rob_helper(nums: &[i64], i: usize, prev2: i64, prev1: i64) -> i64 {
    if i >= nums.len() {
        return prev1;
    }
    let take: i64 = prev2 + nums[i];
    let mut cur: i64 = prev1;
    if take > cur {
        cur = take;
    }
    rob_helper(nums, i + 1, prev1, cur)
}

pub fn rob(nums: &[i64]) -> i64 {
    rob_helper(nums, 0, 0, 0)
}
