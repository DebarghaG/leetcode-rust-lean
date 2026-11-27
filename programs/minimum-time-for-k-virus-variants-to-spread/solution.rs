fn can_spread(
    points: &[Vec<i64>],
    k: i64,
    minx: i64,
    maxx: i64,
    miny: i64,
    maxy: i64,
    days: i64,
) -> bool {
    let n = points.len();
    let mut found = false;
    let mut cx = minx;
    while cx <= maxx {
        let mut cy = miny;
        while cy <= maxy {
            let mut count: i64 = 0;
            let mut i: usize = 0;
            while i < n {
                let row = &points[i];
                let px = row[0];
                let py = row[1];

                let dx = if cx >= px { cx - px } else { px - cx };
                let dy = if cy >= py { cy - py } else { py - cy };

                if dx + dy <= days {
                    count += 1;
                }
                i += 1;
            }

            if count >= k {
                found = true;
            }

            cy += 1;
        }
        cx += 1;
    }
    found
}

pub fn min_daysk_variants(points: &[Vec<i64>], k: i64) -> i64 {
    let n = points.len();

    let mut minx = points[0][0];
    let mut maxx = points[0][0];
    let mut miny = points[0][1];
    let mut maxy = points[0][1];

    let mut i: usize = 1;
    while i < n {
        let row = &points[i];
        let x = row[0];
        let y = row[1];

        if x < minx {
            minx = x;
        }
        if x > maxx {
            maxx = x;
        }
        if y < miny {
            miny = y;
        }
        if y > maxy {
            maxy = y;
        }

        i += 1;
    }

    let max_days = (maxx - minx) + (maxy - miny);
    let mut lo: i64 = 0;
    let mut hi: i64 = max_days;

    while lo < hi {
        let mid = (lo + hi) / 2;
        if can_spread(points, k, minx, maxx, miny, maxy, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}
