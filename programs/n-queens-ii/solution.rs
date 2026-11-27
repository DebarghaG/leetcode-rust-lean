pub fn total_n_queens(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let n_usize = n as usize;
    let m = 2 * n_usize;

    let mut cols: Vec<bool> = Vec::new();
    let mut d1: Vec<bool> = Vec::new();
    let mut d2: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i < n_usize {
        cols.push(false);
        i += 1;
    }

    i = 0;
    while i < m {
        d1.push(false);
        d2.push(false);
        i += 1;
    }

    let mut chosen: Vec<i64> = Vec::new();
    let mut next_col: Vec<i64> = Vec::new();

    i = 0;
    while i < n_usize {
        chosen.push(0);
        next_col.push(0);
        i += 1;
    }

    let mut count: i64 = 0;
    let mut depth: usize = 0;

    loop {
        if depth == n_usize {
            count += 1;

            depth -= 1;
            let c_i = chosen[depth];
            let c = c_i as usize;
            let row_i = depth as i64;
            let d1_idx = (row_i + c_i) as usize;
            let d2_idx = (row_i - c_i + (n - 1)) as usize;

            cols[c] = false;
            d1[d1_idx] = false;
            d2[d2_idx] = false;
        } else {
            let row = depth;
            let mut placed = false;

            while next_col[row] < n {
                let c_i = next_col[row];
                next_col[row] += 1;

                let c = c_i as usize;
                let row_i = row as i64;
                let d1_idx = (row_i + c_i) as usize;
                let d2_idx = (row_i - c_i + (n - 1)) as usize;

                if !cols[c] && !d1[d1_idx] && !d2[d2_idx] {
                    cols[c] = true;
                    d1[d1_idx] = true;
                    d2[d2_idx] = true;

                    chosen[row] = c_i;
                    depth += 1;

                    if depth < n_usize {
                        next_col[depth] = 0;
                    }

                    placed = true;
                    break;
                }
            }

            if !placed {
                if depth == 0 {
                    break;
                }

                depth -= 1;
                let c_i = chosen[depth];
                let c = c_i as usize;
                let row_i = depth as i64;
                let d1_idx = (row_i + c_i) as usize;
                let d2_idx = (row_i - c_i + (n - 1)) as usize;

                cols[c] = false;
                d1[d1_idx] = false;
                d2[d2_idx] = false;
            }
        }
    }

    count
}
