pub fn min_side_jumps(obstacles: &[i64]) -> i64 {
    let inf: i64 = 1_000_000_000;

    // Minimum side jumps to be at point 0 in lanes 1, 2, 3.
    // The frog starts in lane 2, but may side-jump at point 0.
    let mut a: i64 = 1;
    let mut b: i64 = 0;
    let mut c: i64 = 1;

    let n: usize = obstacles.len();
    let mut i: usize = 1;

    while i < n {
        let x: i64 = obstacles[i];

        if x == 1 {
            a = inf;
        } else if x == 2 {
            b = inf;
        } else if x == 3 {
            c = inf;
        }

        let min_bc = if b < c { b } else { c };
        let min_ac = if a < c { a } else { c };
        let min_ab = if a < b { a } else { b };

        let mut na: i64 = inf;
        let mut nb: i64 = inf;
        let mut nc: i64 = inf;

        if x != 1 {
            let cand = min_bc + 1;
            na = if a < cand { a } else { cand };
        }

        if x != 2 {
            let cand = min_ac + 1;
            nb = if b < cand { b } else { cand };
        }

        if x != 3 {
            let cand = min_ab + 1;
            nc = if c < cand { c } else { cand };
        }

        a = na;
        b = nb;
        c = nc;

        i += 1;
    }

    let m = if a < b { a } else { b };
    if m < c { m } else { c }
}
