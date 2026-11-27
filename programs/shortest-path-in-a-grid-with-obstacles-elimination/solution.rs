pub fn shortest_path(grid: &[Vec<i64>], k: i64) -> i64 {
    let m = grid.len();
    if m == 0 {
        return -1;
    }
    let n = grid[0].len();
    if n == 0 {
        return -1;
    }
    if m == 1 && n == 1 {
        return 0;
    }
    if k < 0 {
        return -1;
    }

    let max_k_i = (m * n) as i64;
    let mut kk = k;
    if kk > max_k_i {
        kk = max_k_i;
    }

    let k_usize = kk as usize;
    let layers = k_usize + 1;
    let total_states = m * n * layers;

    let mut visited: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total_states {
        visited.push(0);
        i += 1;
    }

    let mut qr: Vec<i64> = Vec::new();
    let mut qc: Vec<i64> = Vec::new();
    let mut qrem: Vec<i64> = Vec::new();
    let mut qdist: Vec<i64> = Vec::new();

    qr.push(0);
    qc.push(0);
    qrem.push(kk);
    qdist.push(0);

    let start_idx = k_usize;
    visited[start_idx] = 1;

    let m_i = m as i64;
    let n_i = n as i64;
    let last_r = m_i - 1;
    let last_c = n_i - 1;

    let mut head: usize = 0;
    while head < qr.len() {
        let r_i = qr[head];
        let c_i = qc[head];
        let rem = qrem[head];
        let dist = qdist[head];
        head += 1;

        let r = r_i as usize;
        let c = c_i as usize;

        if r == m - 1 && c == n - 1 {
            return dist;
        }

        let mut d: usize = 0;
        while d < 4 {
            let mut dr: i64 = 0;
            let mut dc: i64 = 0;

            if d == 0 {
                dr = -1;
            } else if d == 1 {
                dr = 1;
            } else if d == 2 {
                dc = -1;
            } else {
                dc = 1;
            }

            let nr_i = r_i + dr;
            let nc_i = c_i + dc;

            if nr_i >= 0 && nr_i < m_i && nc_i >= 0 && nc_i < n_i {
                let nr = nr_i as usize;
                let nc = nc_i as usize;

                let mut cost = grid[nr][nc];
                if nr_i == last_r && nc_i == last_c {
                    cost = 0;
                }

                let nrem = rem - cost;
                if nrem >= 0 {
                    let rem_u = nrem as usize;
                    let idx = (nr * n + nc) * layers + rem_u;

                    if visited[idx] == 0 {
                        visited[idx] = 1;
                        qr.push(nr_i);
                        qc.push(nc_i);
                        qrem.push(nrem);
                        qdist.push(dist + 1);
                    }
                }
            }

            d += 1;
        }
    }

    -1
}
