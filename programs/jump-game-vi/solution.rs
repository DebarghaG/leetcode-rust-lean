pub fn max_result(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    dp.push(nums[0]);

    // Monotonic deque of indices, stored as i64.
    // Elements before `head` are considered removed from the front.
    let mut q: Vec<i64> = Vec::new();
    q.push(0);
    let mut head: usize = 0;

    let ku = k as usize;
    let mut i: usize = 1;

    while i < n {
        while head < q.len() && (q[head] as usize) + ku < i {
            head += 1;
        }

        let best_idx = q[head] as usize;
        let val = dp[best_idx] + nums[i];
        dp.push(val);

        while q.len() > head && dp[q[q.len() - 1] as usize] <= val {
            q.pop();
        }

        q.push(i as i64);
        i += 1;
    }

    dp[n - 1]
}
