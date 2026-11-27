pub fn is_printable(targetGrid: &[Vec<i64>]) -> bool {
    let m = targetGrid.len();
    if m == 0 {
        return true;
    }
    let n = targetGrid[0].len();
    if n == 0 {
        return true;
    }

    let mut max_color: i64 = 0;
    let mut i = 0;
    while i < m {
        let row = &targetGrid[i];
        let mut j = 0;
        while j < n {
            if row[j] > max_color {
                max_color = row[j];
            }
            j += 1;
        }
        i += 1;
    }

    let k = (max_color + 1) as usize;
    let mut present: Vec<bool> = Vec::new();
    let mut min_r: Vec<usize> = Vec::new();
    let mut min_c: Vec<usize> = Vec::new();
    let mut max_r: Vec<usize> = Vec::new();
    let mut max_c: Vec<usize> = Vec::new();

    let mut c = 0;
    while c < k {
        present.push(false);
        min_r.push(m);
        min_c.push(n);
        max_r.push(0);
        max_c.push(0);
        c += 1;
    }

    i = 0;
    while i < m {
        let row = &targetGrid[i];
        let mut j = 0;
        while j < n {
            let col = row[j] as usize;
            present[col] = true;

            if i < min_r[col] {
                min_r[col] = i;
            }
            if i > max_r[col] {
                max_r[col] = i;
            }
            if j < min_c[col] {
                min_c[col] = j;
            }
            if j > max_c[col] {
                max_c[col] = j;
            }

            j += 1;
        }
        i += 1;
    }

    let mut adj: Vec<Vec<bool>> = Vec::new();
    let mut indeg: Vec<i64> = Vec::new();

    c = 0;
    while c < k {
        let mut row_adj: Vec<bool> = Vec::new();
        let mut d = 0;
        while d < k {
            row_adj.push(false);
            d += 1;
        }
        adj.push(row_adj);
        indeg.push(0);
        c += 1;
    }

    c = 0;
    while c < k {
        if present[c] {
            let r0 = min_r[c];
            let r1 = max_r[c];
            let c0 = min_c[c];
            let c1 = max_c[c];

            let mut ii = r0;
            while ii <= r1 {
                let row = &targetGrid[ii];
                let mut jj = c0;
                while jj <= c1 {
                    let d = row[jj] as usize;
                    if d != c {
                        if !adj[c][d] {
                            adj[c][d] = true;
                            indeg[d] = indeg[d] + 1;
                        }
                    }
                    jj += 1;
                }
                ii += 1;
            }
        }
        c += 1;
    }

    let mut total: i64 = 0;
    c = 0;
    while c < k {
        if present[c] {
            total += 1;
        }
        c += 1;
    }

    let mut queue: Vec<usize> = Vec::new();
    c = 0;
    while c < k {
        if present[c] && indeg[c] == 0 {
            queue.push(c);
        }
        c += 1;
    }

    let mut qidx: usize = 0;
    let mut processed: i64 = 0;

    while qidx < queue.len() {
        let color = queue[qidx];
        qidx += 1;
        processed += 1;

        let mut d = 0;
        while d < k {
            if adj[color][d] {
                indeg[d] -= 1;
                if indeg[d] == 0 {
                    queue.push(d);
                }
            }
            d += 1;
        }
    }

    processed == total
}
