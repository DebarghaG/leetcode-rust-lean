pub fn average_height_of_buildings(buildings: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = buildings.len();
    let mut events: Vec<Vec<i64>> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let s = buildings[i][0];
        let e = buildings[i][1];
        let h = buildings[i][2];

        let mut start_event: Vec<i64> = Vec::new();
        start_event.push(s);
        start_event.push(h);
        events.push(start_event);

        let mut end_event: Vec<i64> = Vec::new();
        end_event.push(e);
        end_event.push(-h);
        events.push(end_event);

        i += 1;
    }

    let m = events.len();
    let mut out: Vec<Vec<i64>> = Vec::new();

    if m == 0 {
        return out;
    }

    // Sort event indices by coordinate (and delta) using iterative merge sort.
    let mut idx: Vec<usize> = Vec::new();
    let mut tmp: Vec<usize> = Vec::new();

    let mut z: usize = 0;
    while z < m {
        idx.push(z);
        tmp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < m {
        let step = width * 2;
        let mut left: usize = 0;

        while left < m {
            let mid = if left + width < m { left + width } else { m };
            let right = if left + step < m { left + step } else { m };

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                let ia = idx[a];
                let ib = idx[b];

                let xa = events[ia][0];
                let xb = events[ib][0];
                let da = events[ia][1];
                let db = events[ib][1];

                let take_b = xb < xa || (xb == xa && db < da);

                if take_b {
                    tmp[k] = ib;
                    b += 1;
                } else {
                    tmp[k] = ia;
                    a += 1;
                }
                k += 1;
            }

            while a < mid {
                tmp[k] = idx[a];
                a += 1;
                k += 1;
            }

            while b < right {
                tmp[k] = idx[b];
                b += 1;
                k += 1;
            }

            left += step;
        }

        let mut t: usize = 0;
        while t < m {
            idx[t] = tmp[t];
            t += 1;
        }

        width = step;
    }

    let mut cur_sum: i64 = 0;
    let mut cur_count: i64 = 0;
    let mut prev: i64 = events[idx[0]][0];

    let mut pos: usize = 0;
    while pos < m {
        let x = events[idx[pos]][0];

        if cur_count > 0 && x > prev {
            let avg = cur_sum / cur_count;
            let out_len = out.len();

            if out_len > 0
                && out[out_len - 1][1] == prev
                && out[out_len - 1][2] == avg
            {
                out[out_len - 1][1] = x;
            } else {
                let mut row: Vec<i64> = Vec::new();
                row.push(prev);
                row.push(x);
                row.push(avg);
                out.push(row);
            }
        }

        while pos < m && events[idx[pos]][0] == x {
            let delta = events[idx[pos]][1];
            cur_sum += delta;

            if delta > 0 {
                cur_count += 1;
            } else {
                cur_count -= 1;
            }

            pos += 1;
        }

        prev = x;
    }

    out
}
