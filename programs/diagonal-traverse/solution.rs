pub fn find_diagonal_order(mat: &[Vec<i64>]) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();

    let m = mat.len();
    if m == 0 {
        return out;
    }

    let n = mat[0].len();
    if n == 0 {
        return out;
    }

    let total = m * n;
    let mut r: usize = 0;
    let mut c: usize = 0;
    let mut up: bool = true;
    let mut count: usize = 0;

    while count < total {
        out.push(mat[r][c]);
        count += 1;

        if up {
            if r > 0 && c + 1 < n {
                r -= 1;
                c += 1;
            } else {
                up = false;
                if c + 1 < n {
                    c += 1;
                } else {
                    r += 1;
                }
            }
        } else {
            if r + 1 < m && c > 0 {
                r += 1;
                c -= 1;
            } else {
                up = true;
                if r + 1 < m {
                    r += 1;
                } else {
                    c += 1;
                }
            }
        }
    }

    out
}
