pub fn find_paths(m: i64, n: i64, maxMove: i64, startRow: i64, startColumn: i64) -> i64 {
    let md: i64 = 1000000007;
    let rows = m as usize;
    let cols = n as usize;

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut r = 0;
    while r < rows {
        let mut row: Vec<i64> = Vec::new();
        let mut c = 0;
        while c < cols {
            row.push(0);
            c += 1;
        }
        dp.push(row);
        r += 1;
    }

    let sr = startRow as usize;
    let sc = startColumn as usize;
    dp[sr][sc] = 1;

    let mut ans: i64 = 0;
    let mut step: i64 = 0;

    while step < maxMove {
        let mut next: Vec<Vec<i64>> = Vec::new();
        let mut r2 = 0;
        while r2 < rows {
            let mut row2: Vec<i64> = Vec::new();
            let mut c2 = 0;
            while c2 < cols {
                row2.push(0);
                c2 += 1;
            }
            next.push(row2);
            r2 += 1;
        }

        let mut i = 0;
        while i < rows {
            let mut j = 0;
            while j < cols {
                let ways = dp[i][j];
                if ways != 0 {
                    if i == 0 {
                        ans = (ans + ways) % md;
                    } else {
                        next[i - 1][j] = (next[i - 1][j] + ways) % md;
                    }

                    if i + 1 == rows {
                        ans = (ans + ways) % md;
                    } else {
                        next[i + 1][j] = (next[i + 1][j] + ways) % md;
                    }

                    if j == 0 {
                        ans = (ans + ways) % md;
                    } else {
                        next[i][j - 1] = (next[i][j - 1] + ways) % md;
                    }

                    if j + 1 == cols {
                        ans = (ans + ways) % md;
                    } else {
                        next[i][j + 1] = (next[i][j + 1] + ways) % md;
                    }
                }
                j += 1;
            }
            i += 1;
        }

        dp = next;
        step += 1;
    }

    ans
}
