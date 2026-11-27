pub fn find_right_interval(intervals: &[Vec<i64>]) -> Vec<i64> {
    let n = intervals.len();

    let mut starts: Vec<i64> = Vec::new();
    let mut ids: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    let mut id: i64 = 0;
    while i < n {
        starts.push(intervals[i][0]);
        ids.push(id);
        i += 1;
        id += 1;
    }

    // Bottom-up merge sort by start value, keeping original indices aligned.
    let mut width: usize = 1;
    while width < n {
        let mut new_starts: Vec<i64> = Vec::new();
        let mut new_ids: Vec<i64> = Vec::new();

        let mut base: usize = 0;
        while base < n {
            let mut mid = base + width;
            if mid > n {
                mid = n;
            }

            let mut end = base + width * 2;
            if end > n {
                end = n;
            }

            let mut l = base;
            let mut r = mid;

            while l < mid && r < end {
                if starts[l] <= starts[r] {
                    new_starts.push(starts[l]);
                    new_ids.push(ids[l]);
                    l += 1;
                } else {
                    new_starts.push(starts[r]);
                    new_ids.push(ids[r]);
                    r += 1;
                }
            }

            while l < mid {
                new_starts.push(starts[l]);
                new_ids.push(ids[l]);
                l += 1;
            }

            while r < end {
                new_starts.push(starts[r]);
                new_ids.push(ids[r]);
                r += 1;
            }

            base = end;
        }

        starts = new_starts;
        ids = new_ids;
        width = width * 2;
    }

    let mut ans: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let target = intervals[i][1];

        let mut lo: usize = 0;
        let mut hi: usize = n;

        while lo < hi {
            let mid = (lo + hi) / 2;
            if starts[mid] >= target {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        if lo < n {
            ans.push(ids[lo]);
        } else {
            ans.push(-1);
        }

        i += 1;
    }

    ans
}
