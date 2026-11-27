pub fn max_selected_elements(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    // Working copy of the values.
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    // Bubble sort.  Inner loop advances i by exactly 1 and only conditionally
    // swaps two adjacent cells at the counter index (same shape as the loop
    // that translated successfully before).
    let mut pass: usize = 0;
    while pass + 1 < n {
        i = 0;
        while i + 1 < n {
            if v[i] > v[i + 1] {
                let t = v[i];
                v[i] = v[i + 1];
                v[i + 1] = t;
            }
            i += 1;
        }
        pass += 1;
    }

    // Build groups of equal values (sorted, so equal values are adjacent).
    // Counts are capped at 2: a value w can only be placed at w or w+1, so at
    // most two copies of w can ever participate in one consecutive run.
    let mut gval: Vec<i64> = Vec::new();
    let mut gcnt: Vec<i64> = Vec::new();
    let mut m: usize = 0;

    i = 0;
    while i < n {
        if i == 0 {
            gval.push(v[0]);
            gcnt.push(1);
            m = 1;
        } else {
            if v[i] == v[i - 1] {
                if gcnt[m - 1] < 2 {
                    gcnt[m - 1] = gcnt[m - 1] + 1;
                }
            } else {
                gval.push(v[i]);
                gcnt.push(1);
                m = m + 1;
            }
        }
        i += 1;
    }

    // Linear DP over groups.
    //   dplo[g] = best run length ending exactly at integer gval[g]
    //   dphi[g] = best run length ending exactly at integer gval[g] + 1
    // Reads of dplo[g-1] / dphi[g-1] mirror the "read dp0[x-1]" shape that
    // already translated.  Values are only ever assigned (no shuffling).
    let mut dplo: Vec<i64> = Vec::new();
    let mut dphi: Vec<i64> = Vec::new();
    let mut ans: i64 = 0;

    let mut g: usize = 0;
    while g < m {
        let cap = gcnt[g];
        let mut lo: i64 = 0;
        let mut hi: i64 = 0;

        if g == 0 {
            lo = 1;
            if cap >= 2 {
                hi = 2;
            } else {
                hi = 1;
            }
        } else {
            let pd = gval[g - 1];
            let plo = dplo[g - 1];
            let phi = dphi[g - 1];
            let gap = gval[g] - pd;

            if gap == 1 {
                lo = plo + 1;
                if phi > lo {
                    lo = phi;
                }
            } else if gap == 2 {
                lo = phi + 1;
            } else {
                lo = 1;
            }

            hi = 1;
            if cap >= 2 {
                if lo + 1 > hi {
                    hi = lo + 1;
                }
            }
            if gap == 1 {
                if phi + 1 > hi {
                    hi = phi + 1;
                }
            }
        }

        if lo > ans {
            ans = lo;
        }
        if hi > ans {
            ans = hi;
        }

        dplo.push(lo);
        dphi.push(hi);
        g += 1;
    }

    ans
}
