pub fn minimum_relative_losses(prices: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = prices.len();

    // Copy prices into a mutable vector for sorting.
    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(prices[i]);
        i += 1;
    }

    // Bottom-up merge sort.
    let mut temp: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < n {
        temp.push(0);
        z += 1;
    }

    let mut width = 1usize;
    while width < n {
        let mut start = 0usize;
        while start < n {
            let mid = if start + width < n {
                start + width
            } else {
                n
            };
            let end = if start + 2 * width < n {
                start + 2 * width
            } else {
                n
            };

            let mut p = start;
            let mut q = mid;
            let mut w = start;

            while p < mid && q < end {
                if a[p] <= a[q] {
                    temp[w] = a[p];
                    p += 1;
                } else {
                    temp[w] = a[q];
                    q += 1;
                }
                w += 1;
            }
            while p < mid {
                temp[w] = a[p];
                p += 1;
                w += 1;
            }
            while q < end {
                temp[w] = a[q];
                q += 1;
                w += 1;
            }

            start = end;
        }

        let mut j = 0;
        while j < n {
            a[j] = temp[j];
            j += 1;
        }

        width = width * 2;
    }

    // Prefix sums of sorted prices.
    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);
    let mut i = 0;
    while i < n {
        pref.push(pref[i] + a[i]);
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let qn = queries.len();
    let mut qi = 0;

    while qi < qn {
        let k = queries[qi][0];
        let m = queries[qi][1] as usize;

        // pos = number of prices <= k.
        let mut lo = 0usize;
        let mut hi = n;
        while lo < hi {
            let mid = (lo + hi) / 2;
            if a[mid] <= k {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let pos = lo;
        let above = n - pos;

        // x = number chosen from the <= k group.
        let mut left = 0usize;
        if m > above {
            left = m - above;
        }

        let mut right = m;
        if pos < right {
            right = pos;
        }

        // The cost is convex in x; find the first x with nonnegative
        // forward difference.
        let mut x = left;
        if left < right {
            let mut lo2 = left;
            let mut hi2 = right;

            while lo2 < hi2 {
                let mid = (lo2 + hi2) / 2;
                let idx2 = n - m + mid;
                let delta = a[mid] + a[idx2] - 2 * k;

                if delta < 0 {
                    lo2 = mid + 1;
                } else {
                    hi2 = mid;
                }
            }

            x = lo2;
        }

        let b = m - x;
        let sum_above = pref[n] - pref[n - b];
        let cost = pref[x] + (b as i64) * 2 * k - sum_above;

        ans.push(cost);
        qi += 1;
    }

    ans
}
