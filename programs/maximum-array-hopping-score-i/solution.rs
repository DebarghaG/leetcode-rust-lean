pub fn max_score(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut dp: Vec<i64> = Vec::new();
    dp.push(0);

    let mut j: usize = 1;
    let mut j_dist: i64 = 1;

    while j < n {
        let mut i: usize = 0;
        let mut dist: i64 = j_dist;
        let mut best: i64 = 0;

        while i < j {
            let cand: i64 = dp[i] + dist * nums[j];
            if cand > best {
                best = cand;
            }
            i += 1;
            dist -= 1;
        }

        dp.push(best);
        j += 1;
        j_dist += 1;
    }

    let ans = dp[n - 1];
    ans
}
