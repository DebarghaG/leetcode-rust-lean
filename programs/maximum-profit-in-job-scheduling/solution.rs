pub fn job_scheduling(startTime: &[i64], endTime: &[i64], profit: &[i64]) -> i64 {
    let n = startTime.len();
    let n_i64 = n as i64;

    // Sort job indices by end time by encoding (endTime, index) into a single i64.
    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        keys.push(endTime[i] * n_i64 + i as i64);
        i += 1;
    }
    keys.sort();

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();
    let mut profits: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        let idx = (keys[i] % n_i64) as usize;
        starts.push(startTime[idx]);
        ends.push(endTime[idx]);
        profits.push(profit[idx]);
        i += 1;
    }

    // dp[i] = maximum profit using the first i jobs in end-time order.
    let mut dp: Vec<i64> = Vec::new();
    dp.push(0);

    i = 0;
    while i < n {
        // Find the largest prefix count p such that ends[p - 1] <= starts[i].
        let mut lo: usize = 0;
        let mut hi: usize = i;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if ends[mid] <= starts[i] {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let p = lo;

        let take = dp[p] + profits[i];
        let skip = dp[i];

        if take > skip {
            dp.push(take);
        } else {
            dp.push(skip);
        }

        i += 1;
    }

    dp[n]
}
