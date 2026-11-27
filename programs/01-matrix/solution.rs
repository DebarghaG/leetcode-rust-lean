pub fn update_matrix(mat: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = mat.len();
    if m == 0 {
        return Vec::new();
    }
    let n = mat[0].len();
    let inf: i64 = 1000000000;

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            if mat[i][j] == 0 {
                row.push(0);
            } else {
                row.push(inf);
            }
            j += 1;
        }
        out.push(row);
        i += 1;
    }

    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            if i > 0 {
                let cand = out[i - 1][j] + 1;
                if cand < out[i][j] {
                    out[i][j] = cand;
                }
            }
            if j > 0 {
                let cand = out[i][j - 1] + 1;
                if cand < out[i][j] {
                    out[i][j] = cand;
                }
            }
            j += 1;
        }
        i += 1;
    }

    i = m;
    while i > 0 {
        i -= 1;
        let mut j = n;
        while j > 0 {
            j -= 1;
            if i + 1 < m {
                let cand = out[i + 1][j] + 1;
                if cand < out[i][j] {
                    out[i][j] = cand;
                }
            }
            if j + 1 < n {
                let cand = out[i][j + 1] + 1;
                if cand < out[i][j] {
                    out[i][j] = cand;
                }
            }
        }
    }

    out
}
