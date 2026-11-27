pub fn min_operations(grid: &[Vec<i64>], x: i64) -> i64 {
    let mut vals: Vec<i64> = Vec::new();

    let m = grid.len();
    let mut i = 0;
    while i < m {
        let row = &grid[i];
        let n = row.len();
        let mut j = 0;
        while j < n {
            vals.push(row[j]);
            j += 1;
        }
        i += 1;
    }

    let total = vals.len();
    if total == 0 {
        return 0;
    }

    let first = vals[0];
    let mut k = 0;
    while k < total {
        if (vals[k] - first) % x != 0 {
            return -1;
        }
        k += 1;
    }

    vals.sort();

    let median = vals[total / 2];
    let mut operations: i64 = 0;

    let mut p = 0;
    while p < total {
        let diff = vals[p] - median;
        if diff >= 0 {
            operations += diff / x;
        } else {
            operations += (-diff) / x;
        }
        p += 1;
    }

    operations
}
