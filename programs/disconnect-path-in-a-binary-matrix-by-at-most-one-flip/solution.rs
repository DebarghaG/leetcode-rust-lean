fn compute_reach(
    grid: &[Vec<i64>],
    m: usize,
    n: usize,
    bi: usize,
    bj: usize,
) -> Vec<bool> {
    let total = m * n;
    let mut r: Vec<bool> = Vec::new();
    let mut k = 0usize;
    while k < total {
        r.push(false);
        k += 1;
    }

    let mut i = 0usize;
    while i < m {
        let mut j = 0usize;
        while j < n {
            let blocked = i == bi && j == bj;
            if !blocked && grid[i][j] == 1 {
                if i == 0 && j == 0 {
                    r[0] = true;
                } else {
                    let mut ok = false;
                    if i > 0 {
                        if r[(i - 1) * n + j] {
                            ok = true;
                        }
                    }
                    if j > 0 {
                        if r[i * n + (j - 1)] {
                            ok = true;
                        }
                    }
                    r[i * n + j] = ok;
                }
            }
            j += 1;
        }
        i += 1;
    }
    r
}

pub fn is_possible_to_cut_path(grid: &[Vec<i64>]) -> bool {
    let m = grid.len();
    if m == 0 {
        return true;
    }
    let n = grid[0].len();
    if n == 0 {
        return true;
    }

    let goal = (m - 1) * n + (n - 1);

    let start_r = compute_reach(grid, m, n, m, n);
    if !start_r[goal] {
        return true;
    }

    // Backtrack a single valid path from the goal to the start.
    let mut path_i: Vec<i64> = Vec::new();
    let mut path_j: Vec<i64> = Vec::new();

    let mut ci = m - 1;
    let mut cj = n - 1;
    let mut steps = 0usize;
    let limit = m * n;
    let mut done = false;

    while steps < limit && !done {
        path_i.push(ci as i64);
        path_j.push(cj as i64);

        if ci == 0 && cj == 0 {
            done = true;
        } else {
            let mut moved = false;
            if ci > 0 {
                if start_r[(ci - 1) * n + cj] {
                    ci = ci - 1;
                    moved = true;
                }
            }
            if !moved && cj > 0 {
                if start_r[ci * n + (cj - 1)] {
                    cj = cj - 1;
                    moved = true;
                }
            }
            if !moved {
                done = true;
            }
        }
        steps += 1;
    }

    // Try removing each interior cell of the path and check connectivity.
    let plen = path_i.len();
    let mut result = false;
    let mut p = 0usize;
    while p < plen && !result {
        let bi = path_i[p] as usize;
        let bj = path_j[p] as usize;

        let is_start = bi == 0 && bj == 0;
        let is_end = bi == m - 1 && bj == n - 1;

        if !is_start && !is_end {
            let r = compute_reach(grid, m, n, bi, bj);
            if !r[goal] {
                result = true;
            }
        }
        p += 1;
    }

    result
}
