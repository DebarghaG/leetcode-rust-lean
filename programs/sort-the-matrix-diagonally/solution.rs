pub fn diagonal_sort(mat: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = mat.len();
    let mut out: Vec<Vec<i64>> = Vec::new();

    if m == 0 {
        return out;
    }

    let n = mat[0].len();

    let mut i: usize = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            row.push(mat[i][j]);
            j += 1;
        }
        out.push(row);
        i += 1;
    }

    let mut c: usize = 0;
    while c < n {
        let mut vals: Vec<i64> = Vec::new();

        let mut r: usize = 0;
        let mut col: usize = c;
        while r < m && col < n {
            vals.push(out[r][col]);
            r += 1;
            col += 1;
        }

        let len = vals.len();
        let mut a: usize = 0;
        while a < len {
            let mut min_i: usize = a;
            let mut b: usize = a + 1;
            while b < len {
                if vals[b] < vals[min_i] {
                    min_i = b;
                }
                b += 1;
            }

            let tmp = vals[a];
            vals[a] = vals[min_i];
            vals[min_i] = tmp;
            a += 1;
        }

        let mut r2: usize = 0;
        let mut col2: usize = c;
        let mut k: usize = 0;
        while r2 < m && col2 < n {
            out[r2][col2] = vals[k];
            r2 += 1;
            col2 += 1;
            k += 1;
        }

        c += 1;
    }

    let mut start_row: usize = 1;
    while start_row < m {
        let mut vals: Vec<i64> = Vec::new();

        let mut r: usize = start_row;
        let mut col: usize = 0;
        while r < m && col < n {
            vals.push(out[r][col]);
            r += 1;
            col += 1;
        }

        let len = vals.len();
        let mut a: usize = 0;
        while a < len {
            let mut min_i: usize = a;
            let mut b: usize = a + 1;
            while b < len {
                if vals[b] < vals[min_i] {
                    min_i = b;
                }
                b += 1;
            }

            let tmp = vals[a];
            vals[a] = vals[min_i];
            vals[min_i] = tmp;
            a += 1;
        }

        let mut r2: usize = start_row;
        let mut col2: usize = 0;
        let mut k: usize = 0;
        while r2 < m && col2 < n {
            out[r2][col2] = vals[k];
            r2 += 1;
            col2 += 1;
            k += 1;
        }

        start_row += 1;
    }

    out
}
