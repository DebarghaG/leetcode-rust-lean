pub fn count_servers(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut row_counts: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        row_counts.push(0);
        i += 1;
    }

    let mut col_counts: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        col_counts.push(0);
        j += 1;
    }

    i = 0;
    while i < m {
        j = 0;
        while j < n {
            if grid[i][j] == 1 {
                row_counts[i] += 1;
                col_counts[j] += 1;
            }
            j += 1;
        }
        i += 1;
    }

    let mut answer: i64 = 0;
    i = 0;
    while i < m {
        j = 0;
        while j < n {
            if grid[i][j] == 1 {
                if row_counts[i] > 1 || col_counts[j] > 1 {
                    answer += 1;
                }
            }
            j += 1;
        }
        i += 1;
    }

    answer
}
