pub fn can_attend_meetings(intervals: &[Vec<i64>]) -> bool {
    let n = intervals.len();
    if n <= 1 {
        return true;
    }

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let row = &intervals[i];
        starts.push(row[0]);
        ends.push(row[1]);
        i += 1;
    }

    let mut i = 1;
    while i < n {
        let start_i = starts[i];
        let end_i = ends[i];
        let mut j = i;

        while j > 0 && starts[j - 1] > start_i {
            starts[j] = starts[j - 1];
            ends[j] = ends[j - 1];
            j -= 1;
        }

        starts[j] = start_i;
        ends[j] = end_i;
        i += 1;
    }

    let mut max_end = ends[0];
    let mut i = 1;
    while i < n {
        if starts[i] < max_end {
            return false;
        }
        if ends[i] > max_end {
            max_end = ends[i];
        }
        i += 1;
    }

    true
}
