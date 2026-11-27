pub fn brightest_position(lights: &[Vec<i64>]) -> i64 {
    let offset: i64 = 1000000000;
    let n = lights.len();

    let mut events: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let pos = lights[i][0];
        let range = lights[i][1];
        let left = pos - range;
        let right = pos + range + 1;

        // Odd event: +1 at start. Even event: -1 at end + 1.
        events.push((left + offset) * 2 + 1);
        events.push((right + offset) * 2);

        i += 1;
    }

    let m = events.len();

    // Iterative bottom-up merge sort of the encoded events.
    let mut tmp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < m {
        tmp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < m {
        let mut left: usize = 0;
        while left < m {
            let mid = if left + width < m { left + width } else { m };
            let right = if left + width * 2 < m {
                left + width * 2
            } else {
                m
            };

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if events[a] <= events[b] {
                    tmp[k] = events[a];
                    a += 1;
                } else {
                    tmp[k] = events[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                tmp[k] = events[a];
                a += 1;
                k += 1;
            }

            while b < right {
                tmp[k] = events[b];
                b += 1;
                k += 1;
            }

            left = left + width * 2;
        }

        let mut p: usize = 0;
        while p < m {
            events[p] = tmp[p];
            p += 1;
        }

        width = width * 2;
    }

    let mut idx: usize = 0;
    let mut cur: i64 = 0;
    let mut best_bright: i64 = -1;
    let mut best_pos: i64 = 0;

    while idx < m {
        let pos_code = events[idx] / 2;
        let pos = pos_code - offset;
        let mut delta: i64 = 0;

        while idx < m && events[idx] / 2 == pos_code {
            if events[idx] % 2 == 1 {
                delta += 1;
            } else {
                delta -= 1;
            }
            idx += 1;
        }

        cur += delta;

        if cur > best_bright {
            best_bright = cur;
            best_pos = pos;
        }
    }

    best_pos
}
