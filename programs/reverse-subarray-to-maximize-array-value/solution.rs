fn abs_i64(x: i64) -> i64 {
    if x < 0 {
        -x
    } else {
        x
    }
}

pub fn max_value_after_reverse(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i + 1 < n {
        total += abs_i64(nums[i + 1] - nums[i]);
        i += 1;
    }

    let first = nums[0];
    let last = nums[n - 1];
    let mut ans = total;

    let a0 = nums[0];
    let b0 = nums[1];
    let mut max_lower = if a0 < b0 { a0 } else { b0 };
    let mut min_upper = if a0 < b0 { b0 } else { a0 };

    i = 0;
    while i + 1 < n {
        let a = nums[i];
        let b = nums[i + 1];
        let d = abs_i64(a - b);

        let prefix_gain = abs_i64(first - b) - d;
        let prefix_candidate = total + prefix_gain;
        if prefix_candidate > ans {
            ans = prefix_candidate;
        }

        let suffix_gain = abs_i64(a - last) - d;
        let suffix_candidate = total + suffix_gain;
        if suffix_candidate > ans {
            ans = suffix_candidate;
        }

        let low = if a < b { a } else { b };
        let high = if a < b { b } else { a };

        if low > max_lower {
            max_lower = low;
        }
        if high < min_upper {
            min_upper = high;
        }

        i += 1;
    }

    if max_lower > min_upper {
        let internal_candidate = total + 2 * (max_lower - min_upper);
        if internal_candidate > ans {
            ans = internal_candidate;
        }
    }

    ans
}
