pub fn special_perm(nums: &[i64]) -> i64 {
    let n = nums.len();
    let total: usize = 1usize << n;
    let modv: i64 = 1000000007;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total * n {
        dp.push(0);
        i += 1;
    }

    let mut start: usize = 0;
    while start < n {
        let mask: usize = 1usize << start;
        dp[mask * n + start] = 1;
        start += 1;
    }

    let mut mask: usize = 1;
    while mask < total {
        let mut last: usize = 0;
        while last < n {
            let cur = dp[mask * n + last];
            if cur != 0 {
                let mut nxt: usize = 0;
                while nxt < n {
                    if (mask & (1usize << nxt)) == 0 {
                        let a = nums[last];
                        let b = nums[nxt];
                        if a % b == 0 || b % a == 0 {
                            let next_mask: usize = mask | (1usize << nxt);
                            let idx: usize = next_mask * n + nxt;
                            dp[idx] = (dp[idx] + cur) % modv;
                        }
                    }
                    nxt += 1;
                }
            }
            last += 1;
        }
        mask += 1;
    }

    let full: usize = total - 1;
    let mut ans: i64 = 0;
    let mut last: usize = 0;
    while last < n {
        ans = (ans + dp[full * n + last]) % modv;
        last += 1;
    }

    ans
}
