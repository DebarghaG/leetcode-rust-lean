pub fn longest_line(mat: &[Vec<i64>]) -> i64 {
    let m = mat.len();
    if m == 0 {
        return 0;
    }
    let n = mat[0].len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = 0;

    // Horizontal lines
    for i in 0..m {
        let row = &mat[i];
        let mut cur: i64 = 0;
        for j in 0..n {
            if row[j] == 1 {
                cur += 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 0;
            }
        }
    }

    // Vertical lines
    for j in 0..n {
        let mut cur: i64 = 0;
        for i in 0..m {
            if mat[i][j] == 1 {
                cur += 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 0;
            }
        }
    }

    // Diagonal lines: down-right, starting from the top row
    for j in 0..n {
        let mut steps = m;
        let rem = n - j;
        if rem < steps {
            steps = rem;
        }

        let mut cur: i64 = 0;
        for t in 0..steps {
            let r = t;
            let c = j + t;
            if mat[r][c] == 1 {
                cur += 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 0;
            }
        }
    }

    // Diagonal lines: down-right, starting from the left column
    for i in 1..m {
        let mut steps = m - i;
        if n < steps {
            steps = n;
        }

        let mut cur: i64 = 0;
        for t in 0..steps {
            let r = i + t;
            let c = t;
            if mat[r][c] == 1 {
                cur += 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 0;
            }
        }
    }

    // Anti-diagonal lines: down-left, starting from the top row
    for j in 0..n {
        let mut steps = m;
        let rem = j + 1;
        if rem < steps {
            steps = rem;
        }

        let mut cur: i64 = 0;
        for t in 0..steps {
            let r = t;
            let c = j - t;
            if mat[r][c] == 1 {
                cur += 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 0;
            }
        }
    }

    // Anti-diagonal lines: down-left, starting from the right column
    for i in 1..m {
        let mut steps = m - i;
        if n < steps {
            steps = n;
        }

        let mut cur: i64 = 0;
        for t in 0..steps {
            let r = i + t;
            let c = (n - 1) - t;
            if mat[r][c] == 1 {
                cur += 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 0;
            }
        }
    }

    best
}
