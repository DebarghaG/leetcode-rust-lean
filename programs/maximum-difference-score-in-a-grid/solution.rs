pub fn max_score(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    let n = grid[0].len();
    let inf: i64 = 1000000000;

    let mut top: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        top.push(inf);
        j += 1;
    }

    let mut ans: i64 = -1000000000;
    let mut i: usize = 0;
    while i < m {
        let mut left: i64 = inf;
        j = 0;
        while j < n {
            let mut prev_min: i64 = top[j];
            if left < prev_min {
                prev_min = left;
            }

            if prev_min != inf {
                let cand: i64 = grid[i][j] - prev_min;
                if cand > ans {
                    ans = cand;
                }
            }

            let cur: i64 = grid[i][j];
            if cur < left {
                left = cur;
            }
            if left < top[j] {
                top[j] = left;
            }

            j += 1;
        }
        i += 1;
    }

    ans
}
