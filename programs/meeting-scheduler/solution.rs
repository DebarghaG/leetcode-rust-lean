fn sort_slots(slots: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = slots.len();
    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        starts.push(slots[i][0]);
        ends.push(slots[i][1]);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut new_starts: Vec<i64> = Vec::new();
        let mut new_ends: Vec<i64> = Vec::new();
        let mut left: usize = 0;

        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = left + width + width;
            if right > n {
                right = n;
            }

            let mut a: usize = left;
            let mut b: usize = mid;

            while a < mid && b < right {
                if starts[a] <= starts[b] {
                    new_starts.push(starts[a]);
                    new_ends.push(ends[a]);
                    a += 1;
                } else {
                    new_starts.push(starts[b]);
                    new_ends.push(ends[b]);
                    b += 1;
                }
            }

            while a < mid {
                new_starts.push(starts[a]);
                new_ends.push(ends[a]);
                a += 1;
            }

            while b < right {
                new_starts.push(starts[b]);
                new_ends.push(ends[b]);
                b += 1;
            }

            left = right;
        }

        starts = new_starts;
        ends = new_ends;
        width = width + width;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        row.push(starts[i]);
        row.push(ends[i]);
        out.push(row);
        i += 1;
    }

    out
}

pub fn min_available_duration(slots1: &[Vec<i64>], slots2: &[Vec<i64>], duration: i64) -> Vec<i64> {
    let a = sort_slots(slots1);
    let b = sort_slots(slots2);

    let n = a.len();
    let m = b.len();

    let mut p: usize = 0;
    let mut q: usize = 0;

    while p < n && q < m {
        let s1 = a[p][0];
        let e1 = a[p][1];
        let s2 = b[q][0];
        let e2 = b[q][1];

        let start = if s1 > s2 { s1 } else { s2 };
        let end = if e1 < e2 { e1 } else { e2 };

        if end - start >= duration {
            let mut res: Vec<i64> = Vec::new();
            res.push(start);
            res.push(start + duration);
            return res;
        }

        if e1 < e2 {
            p += 1;
        } else {
            q += 1;
        }
    }

    Vec::new()
}
