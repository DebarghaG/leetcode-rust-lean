fn isqrt_bounded(n: i64, hi0: i64) -> i64 {
    // floor(sqrt(n)) for n >= 0, searching in [0, hi0]
    let mut lo: i64 = 0;
    let mut hi: i64 = hi0;
    while lo < hi {
        let mid: i64 = (lo + hi + 1) / 2;
        if mid * mid <= n {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}

pub fn count_lattice_points(circles: &[Vec<i64>]) -> i64 {
    let n: usize = circles.len();

    // Grid upper bounds matching the standard [0, maxX] x [0, maxY] reference grid.
    let mut maxx: i64 = 0;
    let mut maxy: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let cx: i64 = circles[i][0];
        let cy: i64 = circles[i][1];
        let r: i64 = circles[i][2];
        if cx + r > maxx {
            maxx = cx + r;
        }
        if cy + r > maxy {
            maxy = cy + r;
        }
        i += 1;
    }

    // Difference array over y in [0, maxy]; size maxy+2 to allow index hi+1.
    let ylen: i64 = maxy + 2;
    let mut diff: Vec<i64> = Vec::new();
    let mut t: i64 = 0;
    while t < ylen {
        diff.push(0);
        t += 1;
    }

    let mut total: i64 = 0;
    let mut x: i64 = 0;
    while x <= maxx {
        // Clear the difference array.
        let mut z: i64 = 0;
        while z < ylen {
            diff[z as usize] = 0;
            z += 1;
        }

        // Accumulate each circle's vertical interval at this x (clamped to y >= 0).
        let mut c: usize = 0;
        while c < n {
            let cx: i64 = circles[c][0];
            let cy: i64 = circles[c][1];
            let r: i64 = circles[c][2];
            let dx: i64 = x - cx;
            let d2: i64 = dx * dx;
            let r2: i64 = r * r;
            if d2 <= r2 {
                let dy: i64 = isqrt_bounded(r2 - d2, r);
                let mut lo: i64 = cy - dy;
                let hi: i64 = cy + dy;
                if lo < 0 {
                    lo = 0;
                }
                if hi >= 0 {
                    diff[lo as usize] += 1;
                    diff[(hi + 1) as usize] -= 1;
                }
            }
            c += 1;
        }

        // Sweep the column to count covered lattice points.
        let mut active: i64 = 0;
        let mut y: i64 = 0;
        while y <= maxy {
            active += diff[y as usize];
            if active > 0 {
                total += 1;
            }
            y += 1;
        }

        x += 1;
    }

    total
}
