fn abs_i64(x: i64) -> i64 {
    if x < 0 {
        -x
    } else {
        x
    }
}

fn manhattan(points: &[Vec<i64>], i: usize, j: usize) -> i64 {
    let dx: i64 = points[i][0] - points[j][0];
    let dy: i64 = points[i][1] - points[j][1];
    abs_i64(dx) + abs_i64(dy)
}

// Select the unused vertex with the smallest current best distance.
// The running minimum value and running argmin are written into their own
// array slots at the loop counter (a fold-friendly shape); the chosen index is
// never assigned from the counter into a plain scalar.
fn select_min(best: &[i64], used: &[bool]) -> usize {
    let n: usize = best.len();
    let big: i64 = 1000000000;

    let mut mval: Vec<i64> = Vec::new();
    let mut aidx: Vec<i64> = Vec::new();

    // Seed with index 0.
    let mut cur0: i64 = big;
    if !used[0] {
        cur0 = best[0];
    }
    mval.push(cur0);
    aidx.push(0);

    let mut j: usize = 1;
    while j < n {
        let mut cur: i64 = big;
        if !used[j] {
            cur = best[j];
        }
        let prevmin: i64 = mval[j - 1];
        if cur < prevmin {
            mval.push(cur);
            aidx.push(j as i64);
        } else {
            mval.push(prevmin);
            aidx.push(aidx[j - 1]);
        }
        j += 1;
    }

    let r: i64 = aidx[n - 1];
    r as usize
}

// Relax the best-distance array using edges from the newly added vertex v.
fn relax(best: &mut Vec<i64>, used: &[bool], points: &[Vec<i64>], v: usize) {
    let n: usize = best.len();
    let mut u: usize = 0;
    while u < n {
        if !used[u] {
            let d: i64 = manhattan(points, v, u);
            if d < best[u] {
                best[u] = d;
            }
        }
        u += 1;
    }
}

pub fn min_cost_connect_points(points: &[Vec<i64>]) -> i64 {
    let n: usize = points.len();
    if n <= 1 {
        return 0;
    }

    let mut used: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        used.push(false);
        i += 1;
    }

    let mut best: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        best.push(0);
        i += 1;
    }

    used[0] = true;
    i = 0;
    while i < n {
        best[i] = manhattan(points, 0, i);
        i += 1;
    }

    let mut total: i64 = 0;
    let mut added: usize = 1;

    while added < n {
        let v: usize = select_min(&best, &used);
        total += best[v];
        used[v] = true;
        relax(&mut best, &used, points, v);
        added += 1;
    }

    total
}
