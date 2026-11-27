fn merge_sort_by_key(vals: &Vec<i64>, idx_in: Vec<usize>) -> Vec<usize> {
    let n = idx_in.len();
    let mut idx = idx_in;

    let mut buf: Vec<usize> = Vec::new();
    let mut t = 0;
    while t < n {
        buf.push(idx[t]);
        t += 1;
    }

    if n < 2 {
        return idx;
    }

    let mut width = 1;
    while width < n {
        let mut start = 0;
        while start < n {
            let mid0 = start + width;
            let end0 = start + width + width;
            let mid = if mid0 < n { mid0 } else { n };
            let end = if end0 < n { end0 } else { n };

            let mut a = start;
            let mut b = mid;
            let mut w = start;

            while a < mid && b < end {
                if vals[idx[a]] <= vals[idx[b]] {
                    buf[w] = idx[a];
                    a += 1;
                } else {
                    buf[w] = idx[b];
                    b += 1;
                }
                w += 1;
            }
            while a < mid {
                buf[w] = idx[a];
                a += 1;
                w += 1;
            }
            while b < end {
                buf[w] = idx[b];
                b += 1;
                w += 1;
            }

            start = end;
        }

        let mut i = 0;
        while i < n {
            idx[i] = buf[i];
            i += 1;
        }

        width = width + width;
    }

    idx
}

fn uf_find(parent: &mut Vec<usize>, mut x: usize) -> usize {
    while parent[x] != x {
        let p = parent[x];
        let gp = parent[p];
        parent[x] = gp;
        x = gp;
    }
    x
}

fn uf_union(parent: &mut Vec<usize>, size: &mut Vec<i64>, a: usize, b: usize) {
    let ra = uf_find(parent, a);
    let rb = uf_find(parent, b);
    if ra == rb {
        return;
    }
    if size[ra] < size[rb] {
        parent[ra] = rb;
        let s = size[rb] + size[ra];
        size[rb] = s;
    } else {
        parent[rb] = ra;
        let s = size[ra] + size[rb];
        size[ra] = s;
    }
}

pub fn max_points(grid: &[Vec<i64>], queries: &[i64]) -> Vec<i64> {
    let m = grid.len();
    let n = grid[0].len();
    let total = m * n;
    let k = queries.len();

    // Flatten grid values, and record row/col of each cell (no division needed).
    let mut vals: Vec<i64> = Vec::new();
    let mut rows: Vec<usize> = Vec::new();
    let mut cols: Vec<usize> = Vec::new();

    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            vals.push(grid[i][j]);
            rows.push(i);
            cols.push(j);
            j += 1;
        }
        i += 1;
    }

    // Cell indices sorted by cell value.
    let mut cells: Vec<usize> = Vec::new();
    let mut c = 0;
    while c < total {
        cells.push(c);
        c += 1;
    }
    let cells = merge_sort_by_key(&vals, cells);

    // Query indices sorted by query value.
    let mut qvals: Vec<i64> = Vec::new();
    let mut qi = 0;
    while qi < k {
        qvals.push(queries[qi]);
        qi += 1;
    }
    let mut qidx: Vec<usize> = Vec::new();
    let mut qj = 0;
    while qj < k {
        qidx.push(qj);
        qj += 1;
    }
    let qidx = merge_sort_by_key(&qvals, qidx);

    // Union-find structures.
    let mut parent: Vec<usize> = Vec::new();
    let mut size: Vec<i64> = Vec::new();
    let mut active: Vec<bool> = Vec::new();
    let mut t = 0;
    while t < total {
        parent.push(t);
        size.push(1);
        active.push(false);
        t += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut a0 = 0;
    while a0 < k {
        ans.push(0);
        a0 += 1;
    }

    let mut cp = 0;
    let mut qp = 0;
    while qp < k {
        let orig = qidx[qp];
        let qv = queries[orig];

        // Activate all cells with value strictly less than this query value.
        while cp < total {
            let cell = cells[cp];
            if vals[cell] >= qv {
                break;
            }

            active[cell] = true;
            parent[cell] = cell;
            size[cell] = 1;

            let r = rows[cell];
            let cl = cols[cell];

            if r > 0 {
                let nb = cell - n;
                if active[nb] {
                    uf_union(&mut parent, &mut size, cell, nb);
                }
            }
            if r + 1 < m {
                let nb = cell + n;
                if active[nb] {
                    uf_union(&mut parent, &mut size, cell, nb);
                }
            }
            if cl > 0 {
                let nb = cell - 1;
                if active[nb] {
                    uf_union(&mut parent, &mut size, cell, nb);
                }
            }
            if cl + 1 < n {
                let nb = cell + 1;
                if active[nb] {
                    uf_union(&mut parent, &mut size, cell, nb);
                }
            }

            cp += 1;
        }

        if active[0] {
            let root = uf_find(&mut parent, 0);
            ans[orig] = size[root];
        } else {
            ans[orig] = 0;
        }

        qp += 1;
    }

    ans
}
