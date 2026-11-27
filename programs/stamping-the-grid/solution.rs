pub fn possible_to_stamp(grid: &[Vec<i64>], stampHeight: i64, stampWidth: i64) -> bool {
    let m = grid.len();
    let n = grid[0].len();

    let sh = stampHeight as usize;
    let sw = stampWidth as usize;

    // Prefix sum of the grid, size (m+1) x (n+1)
    let mut pref: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i <= m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j <= n {
            row.push(0);
            j += 1;
        }
        pref.push(row);
        i += 1;
    }

    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            pref[i + 1][j + 1] =
                grid[i][j] + pref[i][j + 1] + pref[i + 1][j] - pref[i][j];
            j += 1;
        }
        i += 1;
    }

    // Difference array, size (m+1) x (n+1)
    let mut diff: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i <= m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j <= n {
            row.push(0);
            j += 1;
        }
        diff.push(row);
        i += 1;
    }

    if sh <= m && sw <= n {
        let rows = m - sh + 1;
        let cols = n - sw + 1;

        let mut r = 0;
        while r < rows {
            let mut c = 0;
            while c < cols {
                let i2 = r + sh;
                let j2 = c + sw;

                let sum =
                    pref[i2][j2] - pref[r][j2] - pref[i2][c] + pref[r][c];

                if sum == 0 {
                    diff[r][c] += 1;
                    diff[i2][c] -= 1;
                    diff[r][j2] -= 1;
                    diff[i2][j2] += 1;
                }

                c += 1;
            }
            r += 1;
        }
    }

    // Reconstruct coverage via 2D prefix sum and verify, no nested returns
    let mut ok = true;
    i = 0;
    while i < m && ok {
        let mut j = 0;
        while j < n && ok {
            let mut val = diff[i][j];

            if i > 0 {
                val += diff[i - 1][j];
            }
            if j > 0 {
                val += diff[i][j - 1];
            }
            if i > 0 && j > 0 {
                val -= diff[i - 1][j - 1];
            }

            diff[i][j] = val;

            if grid[i][j] == 0 && val == 0 {
                ok = false;
            }

            j += 1;
        }
        i += 1;
    }

    ok
}
