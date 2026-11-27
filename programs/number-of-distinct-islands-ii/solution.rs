fn copy_vec(v: &[i64]) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < v.len() {
        out.push(v[i]);
        i += 1;
    }
    out
}

fn vec_eq(a: &[i64], b: &[i64]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn vec_lex_less(a: &[i64], b: &[i64]) -> bool {
    let na = a.len();
    let nb = b.len();
    let mut i = 0;
    while i < na && i < nb {
        if a[i] < b[i] {
            return true;
        }
        if a[i] > b[i] {
            return false;
        }
        i += 1;
    }
    na < nb
}

fn canonical(cells_x: &[i64], cells_y: &[i64]) -> Vec<i64> {
    let k = cells_x.len();
    let mut best: Vec<i64> = Vec::new();
    let mut t = 0;
    while t < 8 {
        let mut tx: Vec<i64> = Vec::new();
        let mut ty: Vec<i64> = Vec::new();

        let mut idx = 0;
        while idx < k {
            let x = cells_x[idx];
            let y = cells_y[idx];

            let mut a: i64 = 0;
            let mut b: i64 = 0;

            if t == 0 {
                a = x;
                b = y;
            } else if t == 1 {
                a = x;
                b = -y;
            } else if t == 2 {
                a = -x;
                b = y;
            } else if t == 3 {
                a = -x;
                b = -y;
            } else if t == 4 {
                a = y;
                b = x;
            } else if t == 5 {
                a = y;
                b = -x;
            } else if t == 6 {
                a = -y;
                b = x;
            } else {
                a = -y;
                b = -x;
            }

            tx.push(a);
            ty.push(b);
            idx += 1;
        }

        let mut min_x = tx[0];
        let mut min_y = ty[0];
        idx = 1;
        while idx < k {
            if tx[idx] < min_x {
                min_x = tx[idx];
            }
            if ty[idx] < min_y {
                min_y = ty[idx];
            }
            idx += 1;
        }

        let mut keys: Vec<i64> = Vec::new();
        idx = 0;
        while idx < k {
            let nx = tx[idx] - min_x;
            let ny = ty[idx] - min_y;
            keys.push(nx * 100 + ny);
            idx += 1;
        }

        let len = keys.len();
        let mut pos = 1;
        while pos < len {
            let val = keys[pos];
            let mut q = pos;
            while q > 0 && keys[q - 1] > val {
                keys[q] = keys[q - 1];
                q -= 1;
            }
            keys[q] = val;
            pos += 1;
        }

        if t == 0 {
            best = copy_vec(&keys);
        } else if vec_lex_less(&keys, &best) {
            best = copy_vec(&keys);
        }

        t += 1;
    }

    best
}

pub fn num_distinct_islands2(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let total = m * n;
    let mut seen: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < total {
        seen.push(0);
        z += 1;
    }

    let mut shapes: Vec<Vec<i64>> = Vec::new();

    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            let start = i * n + j;

            if grid[i][j] == 1 && seen[start] == 0 {
                let mut cells_x: Vec<i64> = Vec::new();
                let mut cells_y: Vec<i64> = Vec::new();
                let mut stack: Vec<usize> = Vec::new();

                stack.push(start);
                seen[start] = 1;

                let mut head = 0;
                while head < stack.len() {
                    let id = stack[head];
                    head += 1;

                    let x = id / n;
                    let y = id % n;

                    cells_x.push(x as i64);
                    cells_y.push(y as i64);

                    if x > 0 {
                        let nx = x - 1;
                        let nid = nx * n + y;
                        if grid[nx][y] == 1 && seen[nid] == 0 {
                            seen[nid] = 1;
                            stack.push(nid);
                        }
                    }

                    if x + 1 < m {
                        let nx = x + 1;
                        let nid = nx * n + y;
                        if grid[nx][y] == 1 && seen[nid] == 0 {
                            seen[nid] = 1;
                            stack.push(nid);
                        }
                    }

                    if y > 0 {
                        let ny = y - 1;
                        let nid = x * n + ny;
                        if grid[x][ny] == 1 && seen[nid] == 0 {
                            seen[nid] = 1;
                            stack.push(nid);
                        }
                    }

                    if y + 1 < n {
                        let ny = y + 1;
                        let nid = x * n + ny;
                        if grid[x][ny] == 1 && seen[nid] == 0 {
                            seen[nid] = 1;
                            stack.push(nid);
                        }
                    }
                }

                let canon = canonical(&cells_x, &cells_y);

                let mut found = false;
                let mut s = 0;
                while s < shapes.len() {
                    if vec_eq(&shapes[s], &canon) {
                        found = true;
                        break;
                    }
                    s += 1;
                }

                if !found {
                    shapes.push(canon);
                }
            }

            j += 1;
        }
        i += 1;
    }

    shapes.len() as i64
}
