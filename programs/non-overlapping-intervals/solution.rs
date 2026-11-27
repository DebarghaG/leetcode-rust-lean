pub fn erase_overlap_intervals(intervals: &[Vec<i64>]) -> i64 {
    let n: usize = intervals.len();
    if n == 0 {
        return 0;
    }

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        starts.push(intervals[i][0]);
        ends.push(intervals[i][1]);
        i += 1;
    }

    // Iterative bottom-up merge sort by interval end.
    let mut width: usize = 1;
    while width < n {
        let mut new_starts: Vec<i64> = Vec::new();
        let mut new_ends: Vec<i64> = Vec::new();

        let mut base: usize = 0;
        while base < n {
            let mid_possible: usize = base + width;
            let mid: usize = if mid_possible < n { mid_possible } else { n };

            let double_width: usize = width + width;
            let hi_possible: usize = base + double_width;
            let hi: usize = if hi_possible < n { hi_possible } else { n };

            let mut left: usize = base;
            let mut right: usize = mid;

            while left < mid && right < hi {
                if ends[left] <= ends[right] {
                    new_starts.push(starts[left]);
                    new_ends.push(ends[left]);
                    left += 1;
                } else {
                    new_starts.push(starts[right]);
                    new_ends.push(ends[right]);
                    right += 1;
                }
            }

            while left < mid {
                new_starts.push(starts[left]);
                new_ends.push(ends[left]);
                left += 1;
            }

            while right < hi {
                new_starts.push(starts[right]);
                new_ends.push(ends[right]);
                right += 1;
            }

            base = hi;
        }

        starts = new_starts;
        ends = new_ends;
        width = width + width;
    }

    // Greedy scan in increasing order of end times.
    let mut removed: i64 = 0;
    let mut last_end: i64 = -1000000000;
    let mut idx: usize = 0;

    while idx < n {
        let start: i64 = starts[idx];
        if start >= last_end {
            last_end = ends[idx];
        } else {
            removed += 1;
        }
        idx += 1;
    }

    removed
}
