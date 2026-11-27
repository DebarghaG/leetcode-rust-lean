pub fn largest_divisible_subset(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    if n == 0 {
        let empty: Vec<i64> = Vec::new();
        return empty;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut copy_i = 0;
    while copy_i < n {
        a.push(nums[copy_i]);
        copy_i += 1;
    }

    // Manual selection sort in ascending order.
    let mut s = 0;
    while s < n {
        let mut min_idx = s;
        let mut j = s + 1;
        while j < n {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        if min_idx != s {
            let tmp = a[s];
            a[s] = a[min_idx];
            a[min_idx] = tmp;
        }
        s += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut prev: Vec<usize> = Vec::new();
    let mut init_i = 0;
    while init_i < n {
        dp.push(1);
        prev.push(n);
        init_i += 1;
    }

    let mut i = 0;
    while i < n {
        // Iterate larger divisors first so ties keep the largest valid predecessor.
        let mut j = i;
        while j > 0 {
            j -= 1;
            if a[i] % a[j] == 0 {
                let candidate = dp[j] + 1;
                if candidate > dp[i] {
                    dp[i] = candidate;
                    prev[i] = j;
                }
            }
        }
        i += 1;
    }

    let mut best = 0;
    let mut scan = 1;
    while scan < n {
        if dp[scan] > dp[best] {
            best = scan;
        }
        scan += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut cur = best;
    while cur < n {
        ans.push(a[cur]);
        cur = prev[cur];
    }

    ans
}
