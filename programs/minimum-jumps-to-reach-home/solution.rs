pub fn minimum_jumps(forbidden: &[i64], a: i64, b: i64, x: i64) -> i64 {
    if x == 0 {
        return 0;
    }

    let mut maxpos = x;
    let mut i = 0;
    while i < forbidden.len() {
        if forbidden[i] > maxpos {
            maxpos = forbidden[i];
        }
        i += 1;
    }

    let limit_i64 = maxpos + a + b;
    let limit = limit_i64 as usize;
    let n = limit + 1;

    let mut blocked: Vec<bool> = Vec::new();
    let mut j = 0;
    while j < n {
        blocked.push(false);
        j += 1;
    }

    i = 0;
    while i < forbidden.len() {
        let p = forbidden[i];
        if p >= 0 && p <= limit_i64 {
            blocked[p as usize] = true;
        }
        i += 1;
    }

    let mut dist_f: Vec<i64> = Vec::new();
    let mut dist_b: Vec<i64> = Vec::new();
    j = 0;
    while j < n {
        dist_f.push(-1);
        dist_b.push(-1);
        j += 1;
    }

    let mut q_pos: Vec<i64> = Vec::new();
    let mut q_back: Vec<bool> = Vec::new();

    q_pos.push(0);
    q_back.push(false);
    dist_f[0] = 0;

    let mut head: usize = 0;
    while head < q_pos.len() {
        let pos = q_pos[head];
        let was_back = q_back[head];
        head += 1;

        let d: i64;
        if was_back {
            d = dist_b[pos as usize];
        } else {
            d = dist_f[pos as usize];
        }

        // Forward jump is always allowed.
        let np_f = pos + a;
        if np_f <= limit_i64 {
            let idx = np_f as usize;
            if !blocked[idx] && dist_f[idx] < 0 {
                if np_f == x {
                    return d + 1;
                }
                dist_f[idx] = d + 1;
                q_pos.push(np_f);
                q_back.push(false);
            }
        }

        // Backward jump is only allowed if the previous jump was not backward.
        if !was_back {
            let np_b = pos - b;
            if np_b >= 0 {
                let idx = np_b as usize;
                if !blocked[idx] && dist_b[idx] < 0 {
                    if np_b == x {
                        return d + 1;
                    }
                    dist_b[idx] = d + 1;
                    q_pos.push(np_b);
                    q_back.push(true);
                }
            }
        }
    }

    -1
}
