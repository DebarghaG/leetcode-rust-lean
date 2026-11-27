pub fn count_of_pairs(n: i64, x: i64, y: i64) -> Vec<i64> {
    let nn = n as usize;
    let inf: i64 = 1000000;

    let mut dist: Vec<Vec<i64>> = Vec::new();

    let mut i = 0;
    while i < nn {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < nn {
            if i == j {
                row.push(0);
            } else {
                row.push(inf);
            }
            j += 1;
        }
        dist.push(row);
        i += 1;
    }

    i = 0;
    while i + 1 < nn {
        dist[i][i + 1] = 1;
        dist[i + 1][i] = 1;
        i += 1;
    }

    let x0 = (x - 1) as usize;
    let y0 = (y - 1) as usize;

    if x0 != y0 {
        dist[x0][y0] = 1;
        dist[y0][x0] = 1;
    }

    let mut k = 0;
    while k < nn {
        let mut a = 0;
        while a < nn {
            let mut b = 0;
            while b < nn {
                let via = dist[a][k] + dist[k][b];
                if via < dist[a][b] {
                    dist[a][b] = via;
                }
                b += 1;
            }
            a += 1;
        }
        k += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    i = 0;
    while i < nn {
        ans.push(0);
        i += 1;
    }

    i = 0;
    while i < nn {
        let mut j = 0;
        while j < nn {
            if i != j {
                let d = dist[i][j];
                let idx = (d - 1) as usize;
                if idx < nn {
                    ans[idx] = ans[idx] + 1;
                }
            }
            j += 1;
        }
        i += 1;
    }

    ans
}
