pub fn survived_robots_healths(positions: &[i64], healths: &[i64], directions: &[u8]) -> Vec<i64> {
    let n = positions.len();
    if n == 0 {
        return Vec::new();
    }

    let m = n as i64 + 1;

    // Encode each robot as position * m + original_index.
    // Since original_index < m and positions are distinct, sorting these
    // encoded values sorts robots by increasing position.
    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        keys.push(positions[i] * m + (i as i64));
        i += 1;
    }

    // Iterative bottom-up merge sort for keys.
    let mut tmp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        i = 0;
        while i < n {
            let mid = if i + width < n { i + width } else { n };
            let end = if mid + width < n { mid + width } else { n };

            let mut l = i;
            let mut r = mid;
            let mut k = i;

            while l < mid && r < end {
                if keys[l] <= keys[r] {
                    tmp[k] = keys[l];
                    l += 1;
                } else {
                    tmp[k] = keys[r];
                    r += 1;
                }
                k += 1;
            }

            while l < mid {
                tmp[k] = keys[l];
                l += 1;
                k += 1;
            }

            while r < end {
                tmp[k] = keys[r];
                r += 1;
                k += 1;
            }

            i = end;
        }

        let mut t: usize = 0;
        while t < n {
            keys[t] = tmp[t];
            t += 1;
        }

        width = width * 2;
    }

    // Mutable copy of healths. A health of 0 means the robot was removed.
    let mut health: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        health.push(healths[i]);
        i += 1;
    }

    // Stack stores original indices of surviving right-moving robots,
    // ordered by increasing position.
    let mut stack: Vec<i64> = Vec::new();

    let mut pos_iter: usize = 0;
    while pos_iter < n {
        let key = keys[pos_iter];
        let idx_i64 = key % m;
        let idx = idx_i64 as usize;

        if directions[idx] == b'L' {
            let mut h = health[idx];

            while h > 0 && stack.len() > 0 {
                let top_pos = stack.len() - 1;
                let j_i64 = stack[top_pos];
                let j = j_i64 as usize;
                let rh = health[j];

                if h < rh {
                    health[j] = rh - 1;
                    h = 0;
                } else if h == rh {
                    health[j] = 0;
                    stack.pop();
                    h = 0;
                } else {
                    health[j] = 0;
                    stack.pop();
                    h = h - 1;
                }
            }

            health[idx] = h;
        } else {
            stack.push(idx_i64);
        }

        pos_iter += 1;
    }

    let mut out: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        if health[i] > 0 {
            out.push(health[i]);
        }
        i += 1;
    }

    out
}
