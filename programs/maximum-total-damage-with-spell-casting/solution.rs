fn sorted_copy(power: &[i64]) -> Vec<i64> {
    let n = power.len();
    let mut a: Vec<i64> = Vec::new();
    let mut idx = 0;
    while idx < n {
        a.push(power[idx]);
        idx += 1;
    }
    if n <= 1 {
        return a;
    }
    // Iterative bottom-up merge sort (no recursion, no std sort).
    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;
        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + 2 * width < n { start + 2 * width } else { n };
            let mut temp: Vec<i64> = Vec::new();
            let mut l = start;
            let mut r = mid;
            while l < mid && r < end {
                if a[l] <= a[r] {
                    temp.push(a[l]);
                    l += 1;
                } else {
                    temp.push(a[r]);
                    r += 1;
                }
            }
            while l < mid {
                temp.push(a[l]);
                l += 1;
            }
            while r < end {
                temp.push(a[r]);
                r += 1;
            }
            let mut k = 0;
            while k < temp.len() {
                a[start + k] = temp[k];
                k += 1;
            }
            start = end;
        }
        width = width * 2;
    }
    a
}

pub fn maximum_total_damage(power: &[i64]) -> i64 {
    let n = power.len();
    if n == 0 {
        return 0;
    }

    let sorted = sorted_copy(power);

    // Compress into distinct values and their multiplicities.
    let mut vals: Vec<i64> = Vec::new();
    let mut cnts: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        let v = sorted[i];
        let mut c: i64 = 0;
        while i < n && sorted[i] == v {
            c += 1;
            i += 1;
        }
        vals.push(v);
        cnts.push(c);
    }

    let m = vals.len();
    let mut dp: Vec<i64> = Vec::new();
    // q is the number of values <= vals[i] - 3 (monotone across i).
    let mut q: usize = 0;
    let mut i = 0;
    while i < m {
        while q < i && vals[q] <= vals[i] - 3 {
            q += 1;
        }
        // Best total using only values strictly compatible with vals[i].
        let take_prev: i64 = if q > 0 { dp[q - 1] } else { 0 };
        let take: i64 = vals[i] * cnts[i] + take_prev;
        let skip: i64 = if i > 0 { dp[i - 1] } else { 0 };
        let cur: i64 = if take > skip { take } else { skip };
        dp.push(cur);
        i += 1;
    }

    dp[m - 1]
}
