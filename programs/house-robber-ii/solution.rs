pub fn rob(nums: &[i64]) -> i64 {
    let n: usize = nums.len();

    if n == 0 {
        return 0;
    }
    if n == 1 {
        return nums[0];
    }

    // We solve the linear "house robber" problem twice:
    //   Case A: only houses with indices 0 .. n-2 are usable (last house excluded)
    //   Case B: only houses with indices 1 .. n-1 are usable (first house excluded)
    //
    // For a linear row we use the "delta" recurrence:
    //   delta[0] = a[0]
    //   delta[i] = max(0, a[i] - delta[i-1])   for i >= 1
    //   answer   = sum of delta[i]
    // This keeps the carried state feed-forward: prev_delta depends only on
    // itself, and total depends on total and prev_delta.

    // ---- Case A: indices 0 ..= n-2 (loop runs for i in 0 .. n-1) ----
    let end_a: usize = n - 1;
    let mut prev_delta_a: i64 = 0;
    let mut total_a: i64 = 0;
    let mut i: usize = 0;
    while i < end_a {
        let x: i64 = nums[i] - prev_delta_a;
        let mut delta: i64 = 0;
        if x > 0 {
            delta = x;
        }
        total_a = total_a + delta;
        prev_delta_a = delta;
        i = i + 1;
    }

    // ---- Case B: indices 1 ..= n-1 (loop runs for j in 1 .. n) ----
    let mut prev_delta_b: i64 = 0;
    let mut total_b: i64 = 0;
    let mut j: usize = 1;
    while j < n {
        let y: i64 = nums[j] - prev_delta_b;
        let mut deltab: i64 = 0;
        if y > 0 {
            deltab = y;
        }
        total_b = total_b + deltab;
        prev_delta_b = deltab;
        j = j + 1;
    }

    if total_a > total_b {
        total_a
    } else {
        total_b
    }
}
