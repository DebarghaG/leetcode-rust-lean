pub fn minimum_time(nums1: &[i64], nums2: &[i64], x: i64) -> i64 {
    let n = nums1.len();

    let mut sum1: i64 = 0;
    let mut sum2: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        sum1 += nums1[i];
        sum2 += nums2[i];
        i += 1;
    }

    if sum1 <= x {
        return 0;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        a.push(nums1[i]);
        b.push(nums2[i]);
        i += 1;
    }

    // Sort pairs by nums2 ascending using selection sort.
    i = 0;
    while i < n {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < n {
            if b[j] < b[min_idx] {
                min_idx = j;
            }
            j += 1;
        }

        if min_idx != i {
            let ta = a[i];
            a[i] = a[min_idx];
            a[min_idx] = ta;

            let tb = b[i];
            b[i] = b[min_idx];
            b[min_idx] = tb;
        }

        i += 1;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= n {
        dp.push(0);
        k += 1;
    }

    i = 0;
    let mut max_selected: i64 = 0;
    while i < n {
        let ai = a[i];
        let bi = b[i];

        max_selected += 1;

        let mut j: usize = i + 1;
        let mut mult: i64 = max_selected;
        while j > 0 {
            let cand = dp[j - 1] + ai + mult * bi;
            if cand > dp[j] {
                dp[j] = cand;
            }
            j -= 1;
            mult -= 1;
        }

        i += 1;
    }

    let mut t: usize = 1;
    let mut ti: i64 = 1;
    while t <= n {
        let total = sum1 + ti * sum2 - dp[t];
        if total <= x {
            return ti;
        }
        t += 1;
        ti += 1;
    }

    -1
}
