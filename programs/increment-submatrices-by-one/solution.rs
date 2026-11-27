pub fn range_add_queries(n: i64, queries: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n_usize: usize = n as usize;
    let size: usize = n_usize + 1;

    let mut diff: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < size {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < size {
            row.push(0);
            j += 1;
        }
        diff.push(row);
        i += 1;
    }

    let mut k: usize = 0;
    while k < queries.len() {
        let q = &queries[k];
        let r1: usize = q[0] as usize;
        let c1: usize = q[1] as usize;
        let r2: usize = q[2] as usize;
        let c2: usize = q[3] as usize;

        diff[r1][c1] += 1;
        diff[r1][c2 + 1] -= 1;
        diff[r2 + 1][c1] -= 1;
        diff[r2 + 1][c2 + 1] += 1;

        k += 1;
    }

    let mut r: usize = 0;
    while r < size {
        let mut c: usize = 0;
        while c < size {
            if r > 0 {
                let above = diff[r - 1][c];
                diff[r][c] += above;
            }
            if c > 0 {
                let left = diff[r][c - 1];
                diff[r][c] += left;
            }
            if r > 0 && c > 0 {
                let diag = diff[r - 1][c - 1];
                diff[r][c] -= diag;
            }
            c += 1;
        }
        r += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut x: usize = 0;
    while x < n_usize {
        let mut row: Vec<i64> = Vec::new();
        let mut y: usize = 0;
        while y < n_usize {
            row.push(diff[x][y]);
            y += 1;
        }
        out.push(row);
        x += 1;
    }

    out
}
