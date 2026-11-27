pub fn sort_matrix(grid: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = grid.len();

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        let row = &grid[i];
        let mut new_row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            new_row.push(row[j]);
            j += 1;
        }
        out.push(new_row);
        i += 1;
    }

    // Diagonals starting from the left column, including the main diagonal.
    // These belong to the bottom-left triangle and must be non-increasing.
    let mut r = 0;
    while r < n {
        let mut diag: Vec<i64> = Vec::new();
        let mut x = r;
        let mut y = 0;
        while x < n && y < n {
            diag.push(out[x][y]);
            x += 1;
            y += 1;
        }

        let mut k = 1;
        while k < diag.len() {
            let key = diag[k];
            let mut p = k;
            while p > 0 && diag[p - 1] < key {
                diag[p] = diag[p - 1];
                p -= 1;
            }
            diag[p] = key;
            k += 1;
        }

        let mut x2 = r;
        let mut y2 = 0;
        let mut k2 = 0;
        while k2 < diag.len() {
            out[x2][y2] = diag[k2];
            x2 += 1;
            y2 += 1;
            k2 += 1;
        }

        r += 1;
    }

    // Diagonals starting from the top row, excluding the main diagonal.
    // These belong to the top-right triangle and must be non-decreasing.
    let mut c = 1;
    while c < n {
        let mut diag: Vec<i64> = Vec::new();
        let mut x = 0;
        let mut y = c;
        while x < n && y < n {
            diag.push(out[x][y]);
            x += 1;
            y += 1;
        }

        let mut k = 1;
        while k < diag.len() {
            let key = diag[k];
            let mut p = k;
            while p > 0 && diag[p - 1] > key {
                diag[p] = diag[p - 1];
                p -= 1;
            }
            diag[p] = key;
            k += 1;
        }

        let mut x2 = 0;
        let mut y2 = c;
        let mut k2 = 0;
        while k2 < diag.len() {
            out[x2][y2] = diag[k2];
            x2 += 1;
            y2 += 1;
            k2 += 1;
        }

        c += 1;
    }

    out
}
