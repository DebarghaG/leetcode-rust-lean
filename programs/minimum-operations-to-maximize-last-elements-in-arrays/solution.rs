pub fn min_operations(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();
    if n == 0 {
        return 0;
    }

    let big = 1_000_000_000_i64;
    let mut ans = big;

    let last1 = nums1[n - 1];
    let last2 = nums2[n - 1];

    // Case 1: do not swap the last elements.
    let mut total = 0_i64;
    let mut ok = true;
    let mut i = 0_usize;
    while i + 1 < n {
        let u = nums1[i];
        let v = nums2[i];

        let keep_ok = u <= last1 && v <= last2;
        if !keep_ok {
            let swap_ok = v <= last1 && u <= last2;
            if swap_ok {
                total += 1;
            } else {
                ok = false;
            }
        }

        i += 1;
    }

    if ok && total < ans {
        ans = total;
    }

    // Case 2: swap the last elements.
    total = 1_i64;
    ok = true;
    i = 0;
    while i + 1 < n {
        let u = nums1[i];
        let v = nums2[i];

        let keep_ok = u <= last2 && v <= last1;
        if !keep_ok {
            let swap_ok = v <= last2 && u <= last1;
            if swap_ok {
                total += 1;
            } else {
                ok = false;
            }
        }

        i += 1;
    }

    if ok && total < ans {
        ans = total;
    }

    if ans == big {
        -1
    } else {
        ans
    }
}
