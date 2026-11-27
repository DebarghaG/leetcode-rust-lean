pub fn min_path_cost(grid: &[Vec<i64>], moveCost: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut prev: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        prev.push(grid[0][j]);
        j += 1;
    }

    let mut r = 1;
    while r < m {
        let mut cur: Vec<i64> = Vec::new();
        let mut col = 0;

        while col < n {
            let mut best = 1_i64 << 60;
            let mut k = 0;

            while k < n {
                let value = grid[r - 1][k];
                let cost = prev[k] + moveCost[value as usize][col];
                if cost < best {
                    best = cost;
                }
                k += 1;
            }

            cur.push(best + grid[r][col]);
            col += 1;
        }

        prev = cur;
        r += 1;
    }

    let mut ans = 1_i64 << 60;
    let mut j2 = 0;
    while j2 < n {
        if prev[j2] < ans {
            ans = prev[j2];
        }
        j2 += 1;
    }

    ans
}
