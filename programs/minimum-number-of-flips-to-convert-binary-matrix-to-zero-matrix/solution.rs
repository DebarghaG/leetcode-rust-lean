pub fn min_flips(mat: &[Vec<i64>]) -> i64 {
    let m = mat.len();
    if m == 0 {
        return 0;
    }

    let n = mat[0].len();
    if n == 0 {
        return 0;
    }

    let cells = m * n;

    let mut target: i64 = 0;
    let mut r: usize = 0;
    while r < m {
        let row = &mat[r];
        let mut c: usize = 0;
        while c < n {
            if row[c] != 0 {
                let idx = r * n + c;
                target = target | (1i64 << idx);
            }
            c += 1;
        }
        r += 1;
    }

    let mut patterns: Vec<i64> = Vec::new();
    r = 0;
    while r < m {
        let mut c: usize = 0;
        while c < n {
            let mut p: i64 = 0;

            p = p | (1i64 << (r * n + c));

            if r > 0 {
                p = p | (1i64 << ((r - 1) * n + c));
            }
            if r + 1 < m {
                p = p | (1i64 << ((r + 1) * n + c));
            }
            if c > 0 {
                p = p | (1i64 << (r * n + (c - 1)));
            }
            if c + 1 < n {
                p = p | (1i64 << (r * n + (c + 1)));
            }

            patterns.push(p);
            c += 1;
        }
        r += 1;
    }

    let mut limit: i64 = 1;
    let mut t: usize = 0;
    while t < cells {
        limit = limit * 2;
        t += 1;
    }

    let mut best: i64 = -1;
    let mut mask: i64 = 0;
    while mask < limit {
        let mut state: i64 = 0;
        let mut cnt: i64 = 0;
        let mut idx: usize = 0;

        while idx < cells {
            if ((mask >> idx) & 1i64) != 0 {
                state = state ^ patterns[idx];
                cnt += 1;
            }
            idx += 1;
        }

        if state == target {
            if best == -1 || cnt < best {
                best = cnt;
            }
        }

        mask += 1;
    }

    best
}
