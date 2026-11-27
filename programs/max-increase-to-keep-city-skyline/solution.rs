pub fn max_increase_keeping_skyline(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }

    let m = grid[0].len();

    let mut row_max: Vec<i64> = Vec::new();
    let mut col_max: Vec<i64> = Vec::new();

    let mut j = 0;
    while j < m {
        col_max.push(0);
        j += 1;
    }

    let mut r = 0;
    while r < n {
        let row = &grid[r];
        let mut rmax: i64 = 0;

        let mut c = 0;
        while c < m {
            let value = row[c];
            if value > rmax {
                rmax = value;
            }
            if value > col_max[c] {
                col_max[c] = value;
            }
            c += 1;
        }

        row_max.push(rmax);
        r += 1;
    }

    let mut total: i64 = 0;

    r = 0;
    while r < n {
        let row = &grid[r];

        let mut c = 0;
        while c < m {
            let rlim = row_max[r];
            let clim = col_max[c];
            let limit = if rlim < clim { rlim } else { clim };
            total += limit - row[c];
            c += 1;
        }

        r += 1;
    }

    total
}
