pub fn insert(intervals: &[Vec<i64>], newInterval: &[i64]) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();

    let mut ns: i64 = newInterval[0];
    let mut ne: i64 = newInterval[1];
    let mut placed: bool = false;

    let n: usize = intervals.len();
    let mut i: usize = 0;

    while i < n {
        let s: i64 = intervals[i][0];
        let e: i64 = intervals[i][1];

        if e < ns {
            let mut row: Vec<i64> = Vec::new();
            row.push(s);
            row.push(e);
            out.push(row);
        } else if s > ne {
            if !placed {
                let mut row: Vec<i64> = Vec::new();
                row.push(ns);
                row.push(ne);
                out.push(row);
                placed = true;
            }

            let mut row2: Vec<i64> = Vec::new();
            row2.push(s);
            row2.push(e);
            out.push(row2);
        } else {
            if s < ns {
                ns = s;
            }
            if e > ne {
                ne = e;
            }
        }

        i += 1;
    }

    if !placed {
        let mut row: Vec<i64> = Vec::new();
        row.push(ns);
        row.push(ne);
        out.push(row);
    }

    out
}
