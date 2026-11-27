pub fn remove_covered_intervals(intervals: &[Vec<i64>]) -> i64 {
    let n = intervals.len();
    if n == 0 {
        return 0;
    }

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        starts.push(intervals[i][0]);
        ends.push(intervals[i][1]);
        i += 1;
    }

    // Selection sort by start ascending, and by end descending when starts are equal.
    let mut i = 0;
    while i < n {
        let mut best = i;
        let mut j = i + 1;
        while j < n {
            let mut take = false;
            if starts[j] < starts[best] {
                take = true;
            } else if starts[j] == starts[best] && ends[j] > ends[best] {
                take = true;
            }

            if take {
                best = j;
            }
            j += 1;
        }

        if best != i {
            let tmp_start = starts[best];
            starts[best] = starts[i];
            starts[i] = tmp_start;

            let tmp_end = ends[best];
            ends[best] = ends[i];
            ends[i] = tmp_end;
        }

        i += 1;
    }

    let mut count: i64 = 1;
    let mut max_end = ends[0];

    let mut k = 1;
    while k < n {
        if ends[k] > max_end {
            count += 1;
            max_end = ends[k];
        }
        k += 1;
    }

    count
}
