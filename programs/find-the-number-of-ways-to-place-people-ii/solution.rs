pub fn number_of_pairs(points: &[Vec<i64>]) -> i64 {
    let n = points.len();

    let mut xs: Vec<i64> = Vec::new();
    let mut ys: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        xs.push(points[i][0]);
        ys.push(points[i][1]);
        i += 1;
    }

    // Sort by x ascending, and for equal x by y descending.
    let mut i: usize = 0;
    while i < n {
        let mut best: usize = i;
        let mut j: usize = i + 1;

        while j < n {
            let xj = xs[j];
            let xb = xs[best];
            let mut take = false;

            if xj < xb {
                take = true;
            } else if xj == xb {
                if ys[j] > ys[best] {
                    take = true;
                }
            }

            if take {
                best = j;
            }

            j += 1;
        }

        if best != i {
            let tx = xs[i];
            xs[i] = xs[best];
            xs[best] = tx;

            let ty = ys[i];
            ys[i] = ys[best];
            ys[best] = ty;
        }

        i += 1;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let yi = ys[i];
        let mut max_seen: i64 = -2000000000;

        let mut j: usize = i + 1;
        while j < n {
            let yj = ys[j];

            if yj <= yi {
                if yj > max_seen {
                    ans += 1;
                    max_seen = yj;
                }
            }

            j += 1;
        }

        i += 1;
    }

    ans
}
