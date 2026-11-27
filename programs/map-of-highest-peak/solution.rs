pub fn highest_peak(isWater: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = isWater.len();
    if m == 0 {
        return Vec::new();
    }

    let n = isWater[0].len();
    let inf: i64 = 1000000;

    let mut height: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            if isWater[i][j] == 1 {
                row.push(0);
            } else {
                row.push(inf);
            }
            j += 1;
        }
        height.push(row);
        i += 1;
    }

    let mut fi: usize = 0;
    while fi < m {
        let mut j: usize = 0;
        while j < n {
            if fi > 0 {
                let cand = height[fi - 1][j] + 1;
                if cand < height[fi][j] {
                    height[fi][j] = cand;
                }
            }
            if j > 0 {
                let cand = height[fi][j - 1] + 1;
                if cand < height[fi][j] {
                    height[fi][j] = cand;
                }
            }
            j += 1;
        }
        fi += 1;
    }

    let mut bi: usize = m;
    while bi > 0 {
        bi -= 1;
        let mut bj: usize = n;
        while bj > 0 {
            bj -= 1;
            if bi + 1 < m {
                let cand = height[bi + 1][bj] + 1;
                if cand < height[bi][bj] {
                    height[bi][bj] = cand;
                }
            }
            if bj + 1 < n {
                let cand = height[bi][bj + 1] + 1;
                if cand < height[bi][bj] {
                    height[bi][bj] = cand;
                }
            }
        }
    }

    height
}
