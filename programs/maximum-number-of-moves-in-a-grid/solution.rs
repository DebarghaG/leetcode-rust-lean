pub fn max_moves(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut r: usize = 0;
    while r < m {
        dp.push(0);
        r += 1;
    }

    let mut best: i64 = 0;
    let mut col: usize = 0;

    while col + 1 < n {
        let mut next: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < m {
            next.push(-1);
            k += 1;
        }

        let mut any: bool = false;
        let mut j: usize = 0;

        while j < m {
            let start = if j == 0 { 0 } else { j - 1 };
            let end = if j + 1 < m { j + 1 } else { m - 1 };
            let next_value = grid[j][col + 1];

            let mut i: usize = start;
            while i <= end {
                if dp[i] >= 0 && next_value > grid[i][col] {
                    let candidate = dp[i] + 1;
                    if candidate > next[j] {
                        next[j] = candidate;
                    }
                }
                i += 1;
            }

            if next[j] >= 0 {
                any = true;
                if next[j] > best {
                    best = next[j];
                }
            }

            j += 1;
        }

        if !any {
            break;
        }

        dp = next;
        col += 1;
    }

    best
}
