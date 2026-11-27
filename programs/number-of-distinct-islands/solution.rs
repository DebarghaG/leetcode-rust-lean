pub fn num_distinct_islands(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut visited: Vec<Vec<bool>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<bool> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(false);
            j += 1;
        }
        visited.push(row);
        i += 1;
    }

    let mut shapes: Vec<Vec<i64>> = Vec::new();

    let mut r = 0;
    while r < m {
        let mut c = 0;
        while c < n {
            if grid[r][c] == 1 && !visited[r][c] {
                let mut stack: Vec<usize> = Vec::new();
                stack.push(r * n + c);
                visited[r][c] = true;

                let mut cells: Vec<usize> = Vec::new();
                let mut min_r: usize = r;
                let mut max_r: usize = r;
                let mut min_c: usize = c;
                let mut max_c: usize = c;

                while stack.len() > 0 {
                    let top = stack.len() - 1;
                    let idx = stack[top];
                    stack.pop();

                    let cr = idx / n;
                    let cc = idx % n;

                    cells.push(cr);
                    cells.push(cc);

                    if cr < min_r {
                        min_r = cr;
                    }
                    if cr > max_r {
                        max_r = cr;
                    }
                    if cc < min_c {
                        min_c = cc;
                    }
                    if cc > max_c {
                        max_c = cc;
                    }

                    if cr > 0 {
                        let nr = cr - 1;
                        if !visited[nr][cc] && grid[nr][cc] == 1 {
                            visited[nr][cc] = true;
                            stack.push(nr * n + cc);
                        }
                    }
                    if cr + 1 < m {
                        let nr = cr + 1;
                        if !visited[nr][cc] && grid[nr][cc] == 1 {
                            visited[nr][cc] = true;
                            stack.push(nr * n + cc);
                        }
                    }
                    if cc > 0 {
                        let nc = cc - 1;
                        if !visited[cr][nc] && grid[cr][nc] == 1 {
                            visited[cr][nc] = true;
                            stack.push(cr * n + nc);
                        }
                    }
                    if cc + 1 < n {
                        let nc = cc + 1;
                        if !visited[cr][nc] && grid[cr][nc] == 1 {
                            visited[cr][nc] = true;
                            stack.push(cr * n + nc);
                        }
                    }
                }

                let h = max_r - min_r + 1;
                let w = max_c - min_c + 1;
                let mut shape: Vec<i64> = Vec::new();
                shape.push(h as i64);
                shape.push(w as i64);

                let mut k = 0;
                while k < h * w {
                    shape.push(0);
                    k += 1;
                }

                let mut p = 0;
                while p < cells.len() {
                    let rr = cells[p];
                    let cc = cells[p + 1];
                    let pos = (rr - min_r) * w + (cc - min_c);
                    shape[2 + pos] = 1;
                    p += 2;
                }

                let mut found = false;
                let mut s = 0;
                while s < shapes.len() {
                    if !found && shape.len() == shapes[s].len() {
                        let mut q = 0;
                        let mut same = true;
                        while q < shape.len() {
                            if shape[q] != shapes[s][q] {
                                same = false;
                            }
                            q += 1;
                        }
                        if same {
                            found = true;
                        }
                    }
                    s += 1;
                }

                if !found {
                    shapes.push(shape);
                }
            }
            c += 1;
        }
        r += 1;
    }

    shapes.len() as i64
}
