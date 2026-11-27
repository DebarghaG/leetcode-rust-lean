pub fn max_increasing_groups(usageLimits: &[i64]) -> i64 {
    let n: usize = usageLimits.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(usageLimits[i]);
        i += 1;
    }

    let mut b: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        b.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;
        while start < n {
            let mut mid: usize = start + width;
            if mid > n {
                mid = n;
            }

            let mut end: usize = start + width + width;
            if end > n {
                end = n;
            }

            let mut l: usize = start;
            let mut r: usize = mid;
            let mut k: usize = start;

            while l < mid && r < end {
                if a[l] <= a[r] {
                    b[k] = a[l];
                    l += 1;
                } else {
                    b[k] = a[r];
                    r += 1;
                }
                k += 1;
            }

            while l < mid {
                b[k] = a[l];
                l += 1;
                k += 1;
            }

            while r < end {
                b[k] = a[r];
                r += 1;
                k += 1;
            }

            start += width + width;
        }

        i = 0;
        while i < n {
            a[i] = b[i];
            i += 1;
        }

        width = width + width;
    }

    let mut total: i64 = 0;
    let mut ans: i64 = 0;

    i = 0;
    while i < n {
        total += a[i];

        let next: i64 = ans + 1;
        let required: i64 = next * (next + 1) / 2;

        if total >= required {
            ans += 1;
        }

        i += 1;
    }

    ans
}
