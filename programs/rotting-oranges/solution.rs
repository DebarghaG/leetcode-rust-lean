pub fn oranges_rotting(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    let n = grid[0].len();

    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut fresh: i64 = 0;
    let mut qr: Vec<i64> = Vec::new();
    let mut qc: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < m {
        let src = &grid[i];
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let v = src[j];
            row.push(v);
            if v == 1 {
                fresh += 1;
            }
            if v == 2 {
                qr.push(i as i64);
                qc.push(j as i64);
            }
            j += 1;
        }
        g.push(row);
        i += 1;
    }

    if fresh == 0 {
        return 0;
    }

    let mut head: usize = 0;
    let mut minutes: i64 = 0;

    while head < qr.len() {
        let layer_size = qr.len() - head;
        let mut k: usize = 0;

        while k < layer_size {
            let r = qr[head];
            let c = qc[head];
            head += 1;

            if r > 0 {
                let nr = (r - 1) as usize;
                let nc = c as usize;
                if g[nr][nc] == 1 {
                    g[nr][nc] = 2;
                    fresh -= 1;
                    qr.push(nr as i64);
                    qc.push(nc as i64);
                }
            }

            if r + 1 < m as i64 {
                let nr = (r + 1) as usize;
                let nc = c as usize;
                if g[nr][nc] == 1 {
                    g[nr][nc] = 2;
                    fresh -= 1;
                    qr.push(nr as i64);
                    qc.push(nc as i64);
                }
            }

            if c > 0 {
                let nr = r as usize;
                let nc = (c - 1) as usize;
                if g[nr][nc] == 1 {
                    g[nr][nc] = 2;
                    fresh -= 1;
                    qr.push(nr as i64);
                    qc.push(nc as i64);
                }
            }

            if c + 1 < n as i64 {
                let nr = r as usize;
                let nc = (c + 1) as usize;
                if g[nr][nc] == 1 {
                    g[nr][nc] = 2;
                    fresh -= 1;
                    qr.push(nr as i64);
                    qc.push(nc as i64);
                }
            }

            k += 1;
        }

        if fresh == 0 {
            return minutes + 1;
        }

        minutes += 1;
    }

    -1
}
