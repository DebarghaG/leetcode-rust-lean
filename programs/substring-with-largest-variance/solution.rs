pub fn largest_variance(s: &[u8]) -> i64 {
    let n = s.len();
    let mut ans: i64 = 0;
    let neg_inf: i64 = -1000000000;

    let mut major_i: i64 = 0;
    while major_i < 26 {
        let mut minor_i: i64 = 0;
        while minor_i < 26 {
            if major_i != minor_i {
                let major: i64 = 97 + major_i;
                let minor: i64 = 97 + minor_i;

                // f: best sum major - minor of a valid substring ending at k-1
                //    that contains at least one minor.
                // g: best sum of a substring ending at k-1 with no minor.
                let mut f: i64 = neg_inf;
                let mut g: i64 = 0;

                let mut k: usize = 0;
                while k < n {
                    let c: i64 = s[k] as i64;

                    if c == major {
                        f = f + 1;
                        g = g + 1;
                    } else if c == minor {
                        let continue_valid: i64 = f - 1;
                        let start_after_previous_minor: i64 = g - 1;
                        if continue_valid > start_after_previous_minor {
                            f = continue_valid;
                        } else {
                            f = start_after_previous_minor;
                        }
                        g = 0;
                    }

                    if f > ans {
                        ans = f;
                    }

                    k += 1;
                }
            }
            minor_i += 1;
        }
        major_i += 1;
    }

    ans
}
