pub fn unique_paths_iii(grid: &[Vec<i64>]) -> i64 {
    let m_usize: usize = grid.len();
    let n_usize: usize = grid[0].len();
    let m: i64 = m_usize as i64;
    let n: i64 = n_usize as i64;

    let mut start: i64 = 0;
    let mut end: i64 = 0;
    let mut all_mask: i64 = 0;

    let mut i: usize = 0;
    while i < m_usize {
        let mut j: usize = 0;
        while j < n_usize {
            let v: i64 = grid[i][j];
            if v != -1 {
                let idx: i64 = (i as i64) * n + (j as i64);
                all_mask = all_mask | (1_i64 << idx);

                if v == 1 {
                    start = idx;
                }
                if v == 2 {
                    end = idx;
                }
            }
            j += 1;
        }
        i += 1;
    }

    let mut count: i64 = 0;

    let mut stack_pos: Vec<i64> = Vec::new();
    let mut stack_mask: Vec<i64> = Vec::new();
    let mut stack_dir: Vec<i64> = Vec::new();

    stack_pos.push(start);
    stack_mask.push(1_i64 << start);
    stack_dir.push(0);

    while !stack_pos.is_empty() {
        let top: usize = stack_pos.len() - 1;
        let d: i64 = stack_dir[top];

        if d >= 4 {
            stack_pos.pop();
            stack_mask.pop();
            stack_dir.pop();
            continue;
        }

        stack_dir[top] = d + 1;

        let pos: i64 = stack_pos[top];
        let mask: i64 = stack_mask[top];

        let r: i64 = pos / n;
        let c: i64 = pos % n;

        let mut nr: i64 = r;
        let mut nc: i64 = c;
        let mut valid: bool = false;

        if d == 0 {
            if r > 0 {
                nr = r - 1;
                nc = c;
                valid = true;
            }
        } else if d == 1 {
            if r + 1 < m {
                nr = r + 1;
                nc = c;
                valid = true;
            }
        } else if d == 2 {
            if c > 0 {
                nr = r;
                nc = c - 1;
                valid = true;
            }
        } else {
            if c + 1 < n {
                nr = r;
                nc = c + 1;
                valid = true;
            }
        }

        if valid {
            let cell: i64 = grid[nr as usize][nc as usize];

            if cell != -1 {
                let nidx: i64 = nr * n + nc;
                let bit: i64 = 1_i64 << nidx;

                if (mask & bit) == 0 {
                    if nidx == end {
                        let new_mask: i64 = mask | bit;
                        if new_mask == all_mask {
                            count += 1;
                        }
                    } else {
                        stack_pos.push(nidx);
                        stack_mask.push(mask | bit);
                        stack_dir.push(0);
                    }
                }
            }
        }
    }

    count
}
