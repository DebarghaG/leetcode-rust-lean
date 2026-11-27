pub fn check_valid_grid(grid: &[Vec<i64>]) -> bool {
    let n = grid.len();
    let mut ok = true;

    // Basic shape / start checks (no returns here).
    if n == 0 || grid[0].len() != n {
        ok = false;
    }
    if ok && grid[0][0] != 0 {
        ok = false;
    }

    let sz = if ok { n * n } else { 0 };
    let sz_i = (n * n) as i64;

    // pos_r[v] / pos_c[v] = coordinates of the cell visited at index v.
    // Initialised to -1 so we can detect duplicates / missing entries.
    let mut pos_r: Vec<i64> = Vec::new();
    let mut pos_c: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < sz {
        pos_r.push(-1);
        pos_c.push(-1);
        k += 1;
    }

    // Record positions, guarding every mutation behind `ok` (no early returns).
    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < n {
            if ok {
                let v = grid[i][j];
                if v < 0 || v >= sz_i {
                    ok = false;
                } else {
                    let vi = v as usize;
                    if pos_r[vi] != -1 {
                        // Duplicate visit index.
                        ok = false;
                    } else {
                        pos_r[vi] = i as i64;
                        pos_c[vi] = j as i64;
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }

    // Validate that every consecutive pair of visits is a knight move.
    let mut t: usize = 0;
    while t + 1 < sz {
        if ok {
            let r0 = pos_r[t];
            let c0 = pos_c[t];
            let r1 = pos_r[t + 1];
            let c1 = pos_c[t + 1];

            if r0 < 0 || c0 < 0 || r1 < 0 || c1 < 0 {
                // Some index was never filled (missing value).
                ok = false;
            } else {
                let dr = r1 - r0;
                let dc = c1 - c0;
                let adr = if dr < 0 { -dr } else { dr };
                let adc = if dc < 0 { -dc } else { dc };
                if !((adr == 1 && adc == 2) || (adr == 2 && adc == 1)) {
                    ok = false;
                }
            }
        }
        t += 1;
    }

    ok
}
