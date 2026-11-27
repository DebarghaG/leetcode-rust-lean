pub fn max_subsequence(nums: &[i64], k: i64) -> Vec<i64> {
    let n: usize = nums.len();
    let ni: i64 = n as i64;

    // Phase 1: find min and max value (running extremes).
    let mut min_v: i64 = nums[0];
    let mut max_v: i64 = nums[0];
    let mut i: usize = 0;
    while i < n {
        if nums[i] < min_v {
            min_v = nums[i];
        }
        if nums[i] > max_v {
            max_v = nums[i];
        }
        i = i + 1;
    }

    // Phase 2: build a frequency table over [min_v, max_v].
    let range: i64 = max_v - min_v;
    let range_usize: usize = range as usize;
    let size: usize = range_usize + 1;

    let mut counts: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c < size {
        counts.push(0);
        c = c + 1;
    }

    let mut i2: usize = 0;
    while i2 < n {
        let idx: usize = (nums[i2] - min_v) as usize;
        counts[idx] = counts[idx] + 1;
        i2 = i2 + 1;
    }

    // Phase 3: threshold = largest value T with (#elements >= T) >= k.
    // Ascending scan; `prefix` = number of elements strictly below current value.
    let mut prefix: i64 = 0;
    let mut thr: i64 = min_v;
    let mut off: usize = 0;
    while off <= range_usize {
        let val: i64 = min_v + (off as i64);
        if ni - prefix >= k {
            thr = val;
        }
        prefix = prefix + counts[off];
        off = off + 1;
    }

    // Phase 4: how many elements are strictly greater than the threshold.
    let mut count_gt: i64 = 0;
    let mut g: usize = 0;
    while g < n {
        if nums[g] > thr {
            count_gt = count_gt + 1;
        }
        g = g + 1;
    }

    let need: i64 = k - count_gt;
    let thr_idx: usize = (thr - min_v) as usize;
    let total_thr: i64 = counts[thr_idx];
    // Keep only the last `need` occurrences of the threshold value.
    let skip_thr: i64 = total_thr - need;

    // Phase 5: emit selected elements in original order.
    let mut out: Vec<i64> = Vec::new();
    let mut seen_thr: i64 = 0;
    let mut i3: usize = 0;
    while i3 < n {
        let x: i64 = nums[i3];
        if x > thr {
            out.push(x);
        } else if x == thr {
            seen_thr = seen_thr + 1;
            if seen_thr > skip_thr {
                out.push(x);
            }
        }
        i3 = i3 + 1;
    }

    out
}
