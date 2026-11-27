pub fn merge(intervals: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = intervals.len();

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        starts.push(intervals[i][0]);
        ends.push(intervals[i][1]);
        i += 1;
    }

    // Insertion sort by interval start.
    let mut i = 1;
    while i < n {
        let s = starts[i];
        let e = ends[i];
        let mut j = i;

        while j > 0 && starts[j - 1] > s {
            starts[j] = starts[j - 1];
            ends[j] = ends[j - 1];
            j -= 1;
        }

        starts[j] = s;
        ends[j] = e;
        i += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();

    if n == 0 {
        return out;
    }

    let mut cur_start = starts[0];
    let mut cur_end = ends[0];

    let mut k = 1;
    while k < n {
        if starts[k] <= cur_end {
            if ends[k] > cur_end {
                cur_end = ends[k];
            }
        } else {
            let mut row: Vec<i64> = Vec::new();
            row.push(cur_start);
            row.push(cur_end);
            out.push(row);

            cur_start = starts[k];
            cur_end = ends[k];
        }
        k += 1;
    }

    let mut row: Vec<i64> = Vec::new();
    row.push(cur_start);
    row.push(cur_end);
    out.push(row);

    out
}
