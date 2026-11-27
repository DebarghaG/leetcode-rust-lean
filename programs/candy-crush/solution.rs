pub fn candy_crush(board: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = board.len();
    let mut n: usize = 0;
    if m > 0 {
        n = board[0].len();
    }

    let mut b: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(board[i][j]);
            j += 1;
        }
        b.push(row);
        i += 1;
    }

    let total = m * n;
    let limit = total + 1;
    let mut round = 0;

    while round < limit {
        let mut mark: Vec<i64> = Vec::new();
        let mut z = 0;
        while z < total {
            mark.push(0);
            z += 1;
        }

        let mut changed = false;

        // Mark horizontal runs of length at least 3.
        let mut r = 0;
        while r < m {
            let mut c = 0;
            while c < n {
                let val = b[r][c];
                if val != 0 {
                    let mut k = c + 1;
                    while k < n && b[r][k] == val {
                        k += 1;
                    }
                    if k - c >= 3 {
                        let mut t = c;
                        while t < k {
                            mark[r * n + t] = 1;
                            t += 1;
                        }
                    }
                    c = k;
                } else {
                    c += 1;
                }
            }
            r += 1;
        }

        // Mark vertical runs of length at least 3.
        let mut c2 = 0;
        while c2 < n {
            let mut r2 = 0;
            while r2 < m {
                let val = b[r2][c2];
                if val != 0 {
                    let mut k = r2 + 1;
                    while k < m && b[k][c2] == val {
                        k += 1;
                    }
                    if k - r2 >= 3 {
                        let mut t = r2;
                        while t < k {
                            mark[t * n + c2] = 1;
                            t += 1;
                        }
                    }
                    r2 = k;
                } else {
                    r2 += 1;
                }
            }
            c2 += 1;
        }

        // Apply all marks simultaneously.
        let mut r3 = 0;
        while r3 < m {
            let mut c3 = 0;
            while c3 < n {
                if mark[r3 * n + c3] != 0 {
                    b[r3][c3] = 0;
                    changed = true;
                }
                c3 += 1;
            }
            r3 += 1;
        }

        if !changed {
            break;
        }

        // Gravity: drop candies down within every column.
        let mut col = 0;
        while col < n {
            let mut read = m;
            let mut write = m;
            while read > 0 {
                read -= 1;
                let v = b[read][col];
                if v != 0 {
                    write -= 1;
                    b[write][col] = v;
                }
            }
            while write > 0 {
                write -= 1;
                b[write][col] = 0;
            }
            col += 1;
        }

        round += 1;
    }

    b
}
