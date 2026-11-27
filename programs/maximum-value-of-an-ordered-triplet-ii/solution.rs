pub fn maximum_triplet_value(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut max_i: i64 = nums[0];
    let mut max_diff: i64 = 0;
    let mut ans: i64 = 0;

    let mut k: usize = 1;
    while k < n {
        let val = max_diff * nums[k];
        if val > ans {
            ans = val;
        }

        let diff = max_i - nums[k];
        if diff > max_diff {
            max_diff = diff;
        }

        if nums[k] > max_i {
            max_i = nums[k];
        }

        k += 1;
    }

    ans
}
