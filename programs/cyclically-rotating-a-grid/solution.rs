pub fn rotate_grid(grid: &[Vec<i64>], k: i64) -> Vec<Vec<i64>> {
    let m = grid.len();
    if m == 0 {
        return Vec::new();
    }
    let n = grid[0].len();

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i0: usize = 0;
    while i0 < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j0: usize = 0;
        while j0 < n {
            row.push(grid[i0][j0]);
            j0 += 1;
        }
        out.push(row);
        i0 += 1;
    }

    let mut min_dim = m;
    if n < min_dim {
        min_dim = n;
    }

    let mut layer: usize = 0;
    while layer < min_dim / 2 {
        let top = layer;
        let bottom = m - 1 - layer;
        let left = layer;
        let right = n - 1 - layer;

        let mut vals: Vec<i64> = Vec::new();

        let mut j = left;
        while j <= right {
            vals.push(grid[top][j]);
            j += 1;
        }

        let mut i = top + 1;
        while i <= bottom {
            vals.push(grid[i][right]);
            i += 1;
        }

        let mut jb = right;
        while jb > left {
            jb -= 1;
            vals.push(grid[bottom][jb]);
        }

        let mut il = bottom;
        while il > top + 1 {
            il -= 1;
            vals.push(grid[il][left]);
        }

        let len = vals.len();
        if len > 0 {
            let len_i64 = len as i64;
            let mut shift_i64 = k % len_i64;
            if shift_i64 < 0 {
                shift_i64 += len_i64;
            }
            let shift = shift_i64 as usize;

            let mut p: usize = 0;

            let mut jt = left;
            while jt <= right {
                let src = (p + shift) % len;
                out[top][jt] = vals[src];
                p += 1;
                jt += 1;
            }

            let mut ir = top + 1;
            while ir <= bottom {
                let src = (p + shift) % len;
                out[ir][right] = vals[src];
                p += 1;
                ir += 1;
            }

            let mut jb2 = right;
            while jb2 > left {
                jb2 -= 1;
                let src = (p + shift) % len;
                out[bottom][jb2] = vals[src];
                p += 1;
            }

            let mut il2 = bottom;
            while il2 > top + 1 {
                il2 -= 1;
                let src = (p + shift) % len;
                out[il2][left] = vals[src];
                p += 1;
            }
        }

        layer += 1;
    }

    out
}
