pub fn max_increasing_cells(mat: &[Vec<i64>]) -> i64 {
    if mat.len() == 0 {
        return 0;
    }

    let m = mat.len();
    let n = mat[0].len();

    if n == 0 {
        return 0;
    }

    let total = m * n;
    let total_i = total as i64;
    let offset: i64 = 1000000;

    let mut cells: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < m {
        let mut j = 0usize;
        while j < n {
            let idx = i * n + j;
            let idx_i = idx as i64;
            let enc = (mat[i][j] + offset) * total_i + idx_i;
            cells.push(enc);
            j += 1;
        }
        i += 1;
    }

    cells.sort();

    let mut rowbest: Vec<i64> = Vec::new();
    let mut r = 0usize;
    while r < m {
        rowbest.push(0);
        r += 1;
    }

    let mut colbest: Vec<i64> = Vec::new();
    let mut c = 0usize;
    while c < n {
        colbest.push(0);
        c += 1;
    }

    let mut ans: i64 = 0;
    let mut temp: Vec<i64> = Vec::new();
    let mut p = 0usize;

    while p < total {
        temp.clear();

        let idx_start_i = cells[p] % total_i;
        let idx_start = idx_start_i as usize;
        let r0 = idx_start / n;
        let c0 = idx_start % n;
        let v0 = mat[r0][c0];

        let mut q = p;
        while q < total {
            let idx_i = cells[q] % total_i;
            let idx = idx_i as usize;
            let row = idx / n;
            let col = idx % n;

            if mat[row][col] != v0 {
                break;
            }

            let mut best = rowbest[row];
            if colbest[col] > best {
                best = colbest[col];
            }

            temp.push(best + 1);
            q += 1;
        }

        let mut t = 0usize;
        let mut q2 = p;

        while t < temp.len() {
            let idx_i = cells[q2] % total_i;
            let idx = idx_i as usize;
            let row = idx / n;
            let col = idx % n;
            let dp = temp[t];

            if dp > rowbest[row] {
                rowbest[row] = dp;
            }
            if dp > colbest[col] {
                colbest[col] = dp;
            }
            if dp > ans {
                ans = dp;
            }

            t += 1;
            q2 += 1;
        }

        p = q;
    }

    ans
}
