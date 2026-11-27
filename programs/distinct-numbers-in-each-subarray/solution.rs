pub fn distinct_numbers(nums: &[i64], k: i64) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();

    if k <= 0 {
        return ans;
    }

    let n = nums.len();
    let kk = k as usize;

    if kk > n {
        return ans;
    }

    // Number of windows = n - k + 1.
    let num_windows = n - kk + 1;

    let mut start: usize = 0;
    while start < num_windows {
        let end = start + kk;

        // Count distinct values inside nums[start..end] by position:
        // an element is "new" iff it does not match any earlier element
        // of the same window.
        let mut distinct: i64 = 0;

        let mut j: usize = start;
        while j < end {
            let cur = nums[j];
            let mut seen: bool = false;

            let mut t: usize = start;
            while t < j {
                if nums[t] == cur {
                    seen = true;
                }
                t += 1;
            }

            if !seen {
                distinct += 1;
            }

            j += 1;
        }

        ans.push(distinct);
        start += 1;
    }

    ans
}
