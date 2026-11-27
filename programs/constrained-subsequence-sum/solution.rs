pub fn constrained_subset_sum(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();

    let mut dq: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        dq.push(0);
        z += 1;
    }

    let mut head: usize = 0;
    let mut tail: usize = 0;
    let mut ans: i64 = nums[0];

    let mut i: usize = 0;
    while i < n {
        let limit: i64 = i as i64 - k;

        while head < tail && dq[head] < limit {
            head += 1;
        }

        let mut best: i64 = 0;
        if head < tail {
            best = dp[dq[head] as usize];
        }

        let mut val: i64 = nums[i];
        if best > 0 {
            val += best;
        }

        dp.push(val);

        if i == 0 {
            ans = val;
        } else if val > ans {
            ans = val;
        }

        while tail > head && dp[dq[tail - 1] as usize] <= val {
            tail -= 1;
        }

        dq[tail] = i as i64;
        tail += 1;

        i += 1;
    }

    ans
}
