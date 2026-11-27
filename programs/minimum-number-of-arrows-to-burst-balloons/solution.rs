fn sort_by_end(mut items: Vec<Vec<i64>>) -> Vec<Vec<i64>> {
    let n = items.len();
    if n <= 1 {
        return items;
    }

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
                let mut take_left: bool = true;

                if items[i][0] > items[j][0] {
                    take_left = false;
                } else if items[i][0] == items[j][0] {
                    if items[i][1] > items[j][1] {
                        take_left = false;
                    }
                }

                if take_left {
                    let e = items[i][0];
                    let s = items[i][1];
                    let mut row: Vec<i64> = Vec::new();
                    row.push(e);
                    row.push(s);
                    merged.push(row);
                    i += 1;
                } else {
                    let e = items[j][0];
                    let s = items[j][1];
                    let mut row: Vec<i64> = Vec::new();
                    row.push(e);
                    row.push(s);
                    merged.push(row);
                    j += 1;
                }
            }

            while i < mid {
                let e = items[i][0];
                let s = items[i][1];
                let mut row: Vec<i64> = Vec::new();
                row.push(e);
                row.push(s);
                merged.push(row);
                i += 1;
            }

            while j < right {
                let e = items[j][0];
                let s = items[j][1];
                let mut row: Vec<i64> = Vec::new();
                row.push(e);
                row.push(s);
                merged.push(row);
                j += 1;
            }

            left = right;
        }

        items = merged;
        width = width + width;
    }

    items
}

pub fn find_min_arrow_shots(points: &[Vec<i64>]) -> i64 {
    let n = points.len();
    if n == 0 {
        return 0;
    }

    let mut intervals: Vec<Vec<i64>> = Vec::new();
    let mut idx: usize = 0;

    while idx < n {
        let start = points[idx][0];
        let end = points[idx][1];

        let mut row: Vec<i64> = Vec::new();
        row.push(end);
        row.push(start);
        intervals.push(row);

        idx += 1;
    }

    let sorted = sort_by_end(intervals);

    let mut arrows: i64 = 1;
    let mut last_end = sorted[0][0];
    let mut k: usize = 1;

    while k < sorted.len() {
        let start = sorted[k][1];

        if start > last_end {
            arrows += 1;
            last_end = sorted[k][0];
        }

        k += 1;
    }

    arrows
}
