pub fn min_meeting_rooms(intervals: &[Vec<i64>]) -> i64 {
    let n: usize = intervals.len();
    if n == 0 {
        return 0;
    }

    let mut min_start: i64 = intervals[0][0];
    let mut max_end: i64 = intervals[0][1];

    let mut i: usize = 1;
    while i < n {
        let s: i64 = intervals[i][0];
        let e: i64 = intervals[i][1];

        if s < min_start {
            min_start = s;
        }
        if e > max_end {
            max_end = e;
        }

        i += 1;
    }

    let size: usize = (max_end + 2) as usize;
    let mut delta: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < size {
        delta.push(0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let s: usize = intervals[i][0] as usize;
        let e: usize = intervals[i][1] as usize;

        delta[s] = delta[s] + 1;
        delta[e] = delta[e] - 1;

        i += 1;
    }

    let mut active: i64 = 0;
    let mut best: i64 = 0;

    let mut t: usize = min_start as usize;
    let limit: usize = max_end as usize;

    while t <= limit {
        active = active + delta[t];
        if active > best {
            best = active;
        }
        t += 1;
    }

    best
}
