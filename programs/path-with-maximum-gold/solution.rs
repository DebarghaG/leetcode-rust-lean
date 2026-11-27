pub fn get_maximum_gold(grid: &[Vec<i64>]) -> i64 {
    if grid.len() == 0 {
        return 0;
    }
    if grid[0].len() == 0 {
        return 0;
    }

    let m = grid.len();
    let n = grid[0].len();
    let total = m * n;

    let mut gold: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            gold.push(grid[i][j]);
            j += 1;
        }
        i += 1;
    }

    let mut best: i64 = 0;
    let mut si = 0;
    while si < m {
        let mut sj = 0;
        while sj < n {
            let start = si * n + sj;

            if gold[start] > 0 {
                let mut visited: Vec<bool> = Vec::new();
                let mut k = 0;
                while k < total {
                    visited.push(false);
                    k += 1;
                }

                let mut cells: Vec<i64> = Vec::new();
                let mut dirs: Vec<i64> = Vec::new();

                visited[start] = true;
                let mut cur_sum = gold[start];
                if cur_sum > best {
                    best = cur_sum;
                }

                cells.push(start as i64);
                dirs.push(0);

                while cells.len() > 0 {
                    let top = cells.len() - 1;
                    let cell_i64 = cells[top];
                    let cell = cell_i64 as usize;
                    let d = dirs[top];

                    if d >= 4 {
                        visited[cell] = false;
                        cur_sum -= gold[cell];
                        let _ = cells.pop();
                        let _ = dirs.pop();
                    } else {
                        dirs[top] = d + 1;

                        let r = cell / n;
                        let c = cell % n;
                        let mut nr = r;
                        let mut nc = c;
                        let mut valid = true;

                        if d == 0 {
                            if r == 0 {
                                valid = false;
                            } else {
                                nr = r - 1;
                            }
                        } else if d == 1 {
                            if r + 1 >= m {
                                valid = false;
                            } else {
                                nr = r + 1;
                            }
                        } else if d == 2 {
                            if c == 0 {
                                valid = false;
                            } else {
                                nc = c - 1;
                            }
                        } else {
                            if c + 1 >= n {
                                valid = false;
                            } else {
                                nc = c + 1;
                            }
                        }

                        if valid {
                            let next = nr * n + nc;
                            if !visited[next] && gold[next] > 0 {
                                visited[next] = true;
                                cur_sum += gold[next];
                                if cur_sum > best {
                                    best = cur_sum;
                                }
                                cells.push(next as i64);
                                dirs.push(0);
                            }
                        }
                    }
                }
            }

            sj += 1;
        }
        si += 1;
    }

    best
}
