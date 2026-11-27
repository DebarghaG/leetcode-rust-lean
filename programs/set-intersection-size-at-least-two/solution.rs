pub fn intersection_size_two(intervals: &[Vec<i64>]) -> i64 {
    let n = intervals.len();

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < n {
        starts.push(intervals[i][0]);
        ends.push(intervals[i][1]);
        i += 1;
    }

    // Sort by end ascending, and for equal ends by start descending.
    let mut i = 1usize;
    while i < n {
        let key_s = starts[i];
        let key_e = ends[i];
        let mut j = i;

        while j > 0 {
            let prev_e = ends[j - 1];
            let prev_s = starts[j - 1];

            let mut shift = false;
            if prev_e > key_e {
                shift = true;
            } else if prev_e == key_e {
                if prev_s < key_s {
                    shift = true;
                }
            }

            if shift {
                ends[j] = prev_e;
                starts[j] = prev_s;
                j -= 1;
            } else {
                break;
            }
        }

        ends[j] = key_e;
        starts[j] = key_s;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut p1: i64 = -1;
    let mut p2: i64 = -1;

    let mut idx = 0usize;
    while idx < n {
        let s = starts[idx];
        let e = ends[idx];

        if s <= p1 {
            // Both p1 and p2 are already inside this interval.
        } else if s <= p2 {
            // Only p2 is inside this interval.
            ans += 1;
            p1 = p2;
            p2 = e;
        } else {
            // Neither is inside this interval.
            ans += 2;
            p1 = e - 1;
            p2 = e;
        }

        idx += 1;
    }

    ans
}
