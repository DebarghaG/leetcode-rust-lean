fn sort_intervals(mut v: Vec<Vec<i64>>) -> Vec<Vec<i64>> {
    let n = v.len();
    let mut width: usize = 1;

    while width < n {
        let mut merged: Vec<Vec<i64>> = Vec::new();
        let mut left: usize = 0;

        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }

            let mut right = left + width + width;
            if right > n {
                right = n;
            }

            let mut i = left;
            let mut j = mid;

            while i < mid && j < right {
                let mut take_i = false;
                let a0 = v[i][0];
                let b0 = v[j][0];

                if a0 < b0 {
                    take_i = true;
                } else if a0 == b0 {
                    let a1 = v[i][1];
                    let b1 = v[j][1];
                    if a1 <= b1 {
                        take_i = true;
                    }
                }

                let take = if take_i { i } else { j };
                let mut row: Vec<i64> = Vec::new();
                row.push(v[take][0]);
                row.push(v[take][1]);
                merged.push(row);

                if take_i {
                    i += 1;
                } else {
                    j += 1;
                }
            }

            while i < mid {
                let mut row: Vec<i64> = Vec::new();
                row.push(v[i][0]);
                row.push(v[i][1]);
                merged.push(row);
                i += 1;
            }

            while j < right {
                let mut row: Vec<i64> = Vec::new();
                row.push(v[j][0]);
                row.push(v[j][1]);
                merged.push(row);
                j += 1;
            }

            left = right;
        }

        v = merged;
        width = width * 2;
    }

    v
}

pub fn min_connected_groups(intervals: &[Vec<i64>], k: i64) -> i64 {
    let n = intervals.len();
    if n == 0 {
        return 0;
    }

    let mut raw: Vec<Vec<i64>> = Vec::new();
    let mut idx: usize = 0;

    while idx < n {
        let mut row: Vec<i64> = Vec::new();
        row.push(intervals[idx][0]);
        row.push(intervals[idx][1]);
        raw.push(row);
        idx += 1;
    }

    let sorted = sort_intervals(raw);

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut cur_start = sorted[0][0];
    let mut cur_end = sorted[0][1];

    let mut i: usize = 1;
    while i < sorted.len() {
        let s = sorted[i][0];
        let e = sorted[i][1];

        if s <= cur_end {
            if e > cur_end {
                cur_end = e;
            }
        } else {
            starts.push(cur_start);
            ends.push(cur_end);
            cur_start = s;
            cur_end = e;
        }

        i += 1;
    }

    starts.push(cur_start);
    ends.push(cur_end);

    let m = starts.len();
    let mut max_count: i64 = 1;

    let mut right: usize = 0;
    let mut left: usize = 0;

    while left < m {
        if right < left {
            right = left;
        }

        while right < m && starts[right] <= ends[left] + k {
            right += 1;
        }

        let count = (right - left) as i64;
        if count > max_count {
            max_count = count;
        }

        left += 1;
    }

    let m_i64 = m as i64;
    m_i64 - max_count + 1
}
