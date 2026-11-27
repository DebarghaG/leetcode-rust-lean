pub fn largest1_bordered_square(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }
    let m = grid[0].len();
    if m == 0 {
        return 0;
    }

    let mut h: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        row.push(0);
        let mut j = 0;
        while j < m {
            let prev = row[j];
            row.push(prev + grid[i][j]);
            j += 1;
        }
        h.push(row);
        i += 1;
    }

    let mut v: Vec<Vec<i64>> = Vec::new();
    let mut zero_row: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < m {
        zero_row.push(0);
        j += 1;
    }
    v.push(zero_row);

    i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        j = 0;
        while j < m {
            let prev = v[i][j];
            row.push(prev + grid[i][j]);
            j += 1;
        }
        v.push(row);
        i += 1;
    }

    let min_dim = if n < m { n } else { m };
    let mut result: i64 = 0;
    let mut found: bool = false;
    let mut side = min_dim;

    while side > 0 {
        if !found {
            let s = side as i64;
            let mut r = 0;
            while r + side <= n {
                if !found {
                    let mut c = 0;
                    while c + side <= m {
                        if !found {
                            let top = h[r][c + side] - h[r][c];
                            let bottom =
                                h[r + side - 1][c + side] - h[r + side - 1][c];
                            let left = v[r + side][c] - v[r][c];
                            let right =
                                v[r + side][c + side - 1] - v[r][c + side - 1];

                            if top == s && bottom == s && left == s && right == s {
                                result = s * s;
                                found = true;
                            }
                        }
                        c += 1;
                    }
                }
                r += 1;
            }
        }
        side -= 1;
    }

    result
}
