fn neighbor(u: i64, dir: i64, m: i64, n: i64, grid: &[Vec<i64>]) -> i64 {
    let i = u / n;
    let j = u % n;
    let mut r = -1;
    if dir == 0 {
        if i > 0 && grid[(i - 1) as usize][j as usize] == 1 {
            r = (i - 1) * n + j;
        }
    } else if dir == 1 {
        if i + 1 < m && grid[(i + 1) as usize][j as usize] == 1 {
            r = (i + 1) * n + j;
        }
    } else if dir == 2 {
        if j > 0 && grid[i as usize][(j - 1) as usize] == 1 {
            r = i * n + (j - 1);
        }
    } else {
        if j + 1 < n && grid[i as usize][(j + 1) as usize] == 1 {
            r = i * n + (j + 1);
        }
    }
    r
}

pub fn minimum_operations(grid: &[Vec<i64>]) -> i64 {
    let m_usize = grid.len();
    if m_usize == 0 {
        return 0;
    }
    let n_usize = grid[0].len();
    if n_usize == 0 {
        return 0;
    }

    let m = m_usize as i64;
    let n = n_usize as i64;
    let total = m_usize * n_usize;

    // Bipartite graph by checkerboard coloring (i+j parity).
    // Minimum vertex cover == maximum matching (König).
    let mut match_left: Vec<i64> = Vec::new();
    let mut match_right: Vec<i64> = Vec::new();
    let mut visited_stamp: Vec<i64> = Vec::new();
    let mut parent_v: Vec<i64> = Vec::new();
    let mut parent_u: Vec<i64> = Vec::new();

    let mut idx = 0;
    while idx < total {
        match_left.push(-1);
        match_right.push(-1);
        visited_stamp.push(0);
        parent_v.push(-1);
        parent_u.push(-1);
        idx += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    let mut qinit = 0;
    while qinit < total + 1 {
        queue.push(0);
        qinit += 1;
    }

    let mut matching: i64 = 0;
    let mut stamp: i64 = 0;

    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            let ui = i as usize;
            let uj = j as usize;
            let u0 = i * n + j;

            if grid[ui][uj] == 1 && (i + j) % 2 == 0 && match_left[u0 as usize] == -1 {
                stamp += 1;
                parent_u[u0 as usize] = -1;

                queue[0] = u0;
                let mut qhead: usize = 0;
                let mut qtail: usize = 1;
                let mut found_v: i64 = -1;

                while qhead < qtail && found_v == -1 {
                    let u = queue[qhead];
                    qhead += 1;

                    let mut dir = 0;
                    while dir < 4 && found_v == -1 {
                        let v = neighbor(u, dir, m, n, grid);

                        if v != -1 && visited_stamp[v as usize] != stamp {
                            visited_stamp[v as usize] = stamp;
                            parent_v[v as usize] = u;

                            if match_right[v as usize] == -1 {
                                found_v = v;
                            } else {
                                let u2 = match_right[v as usize];
                                parent_u[u2 as usize] = v;
                                queue[qtail] = u2;
                                qtail += 1;
                            }
                        }

                        dir += 1;
                    }
                }

                if found_v != -1 {
                    let mut v = found_v;
                    while v != -1 {
                        let u = parent_v[v as usize];
                        let prev = parent_u[u as usize];
                        match_left[u as usize] = v;
                        match_right[v as usize] = u;
                        v = prev;
                    }
                    matching += 1;
                }
            }

            j += 1;
        }
        i += 1;
    }

    matching
}
