pub fn delete_and_earn(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    // Copy into an owned vector (position-indexed, size n).
    let mut s: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        s.push(nums[i]);
        i += 1;
    }

    // Selection sort (ascending). Loop conditions are purely scalar.
    i = 0;
    while i < n {
        let mut minidx: usize = i;
        let mut j: usize = i + 1;
        while j < n {
            if s[j] < s[minidx] {
                minidx = j;
            }
            j += 1;
        }
        let tmp = s[i];
        s[i] = s[minidx];
        s[minidx] = tmp;
        i += 1;
    }

    // Compress equal values into buckets: vals[k] = distinct value,
    // sums[k] = that value times its count. Only `i` and `m` are
    // loop-carried scalars (both monotone); buckets live in the Vecs.
    let mut vals: Vec<i64> = Vec::new();
    let mut sums: Vec<i64> = Vec::new();
    vals.push(s[0]);
    sums.push(s[0]);
    let mut m: usize = 1;
    i = 1;
    while i < n {
        let v = s[i];
        let last = vals[m - 1];
        if v == last {
            let old = sums[m - 1];
            sums[m - 1] = old + v;
        } else {
            vals.push(v);
            sums.push(v);
            m += 1;
        }
        i += 1;
    }

    // DP over the compressed buckets. dp[g] = best score using buckets 0..=g.
    // Only `g` is a loop-carried scalar; per-step results go into `dp`.
    let mut dp: Vec<i64> = Vec::new();
    let mut g: usize = 0;
    while g < m {
        let mut base: i64 = 0;
        if g >= 1 {
            base = dp[g - 1];
            if vals[g] == vals[g - 1] + 1 {
                if g >= 2 {
                    base = dp[g - 2];
                } else {
                    base = 0;
                }
            }
        }
        let take = sums[g] + base;
        let mut best = take;
        if g >= 1 {
            let skip = dp[g - 1];
            if skip > best {
                best = skip;
            }
        }
        dp.push(best);
        g += 1;
    }

    dp[m - 1]
}
