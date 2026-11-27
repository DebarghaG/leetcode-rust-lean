fn merge_sort_codes(v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    let mut cur: Vec<i64> = v;
    let mut width: usize = 1;

    while width < n {
        let mut next: Vec<i64> = Vec::new();
        let mut start: usize = 0;
        let two_width = width * 2;

        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + two_width < n { start + two_width } else { n };

            let mut i = start;
            let mut j = mid;

            while i < mid && j < end {
                if cur[i] <= cur[j] {
                    next.push(cur[i]);
                    i = i + 1;
                } else {
                    next.push(cur[j]);
                    j = j + 1;
                }
            }

            while i < mid {
                next.push(cur[i]);
                i = i + 1;
            }

            while j < end {
                next.push(cur[j]);
                j = j + 1;
            }

            start = start + two_width;
        }

        cur = next;
        width = width * 2;
    }

    cur
}

pub fn minimum_seconds(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let n64 = n as i64;
    let mut codes: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        codes.push(nums[i] * n64 + (i as i64));
        i = i + 1;
    }

    let sorted = merge_sort_codes(codes);
    let mut ans: i64 = n64;
    let mut gstart: usize = 0;

    while gstart < n {
        let val = sorted[gstart] / n64;
        let mut gend: usize = gstart;

        while gend < n && sorted[gend] / n64 == val {
            gend = gend + 1;
        }

        let first_idx = (sorted[gstart] % n64) as usize;
        let mut prev: usize = first_idx;
        let mut max_gap: i64 = 0;
        let mut t: usize = gstart + 1;

        while t < gend {
            let cur_idx = (sorted[t] % n64) as usize;
            let gap = (cur_idx as i64) - (prev as i64);

            if gap > max_gap {
                max_gap = gap;
            }

            prev = cur_idx;
            t = t + 1;
        }

        let wrap_gap = (first_idx as i64) + n64 - (prev as i64);
        if wrap_gap > max_gap {
            max_gap = wrap_gap;
        }

        let candidate = max_gap / 2;
        if candidate < ans {
            ans = candidate;
        }

        gstart = gend;
    }

    ans
}
