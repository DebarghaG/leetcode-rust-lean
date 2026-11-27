pub fn min_score(grid: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = grid.len();
    let n = grid[0].len();
    let total = m * n;
    let base = total as i64;

    let mut cells: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            let idx = (i * n + j) as i64;
            let code = grid[i][j] * base + idx;
            cells.push(code);
            j += 1;
        }
        i += 1;
    }

    cells.sort();

    let mut row_max: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        row_max.push(0);
        i += 1;
    }

    let mut col_max: Vec<i64> = Vec::new();
    let mut j0 = 0;
    while j0 < n {
        col_max.push(0);
        j0 += 1;
    }

    let mut ranks: Vec<i64> = Vec::new();
    i = 0;
    while i < total {
        ranks.push(0);
        i += 1;
    }

    let mut k = 0;
    while k < cells.len() {
        let code = cells[k];
        let idx64 = code % base;
        let idx = idx64 as usize;
        let r = idx / n;
        let c = idx % n;

        let mut best = row_max[r];
        if col_max[c] > best {
            best = col_max[c];
        }
        let rank = best + 1;

        ranks[idx] = rank;
        row_max[r] = rank;
        col_max[c] = rank;

        k += 1;
    }

    let mut ans: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(ranks[i * n + j]);
            j += 1;
        }
        ans.push(row);
        i += 1;
    }

    ans
}
