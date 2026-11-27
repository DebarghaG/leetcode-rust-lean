fn abs_diff(a: i64, b: i64) -> i64 {
    let d = a - b;
    if d < 0 {
        -d
    } else {
        d
    }
}

pub fn min_distance(
    height: i64,
    width: i64,
    tree: &[i64],
    squirrel: &[i64],
    nuts: &[Vec<i64>],
) -> i64 {
    let _ = height;
    let _ = width;

    let tr = tree[0];
    let tc = tree[1];
    let sr = squirrel[0];
    let sc = squirrel[1];

    let n = nuts.len();
    if n == 0 {
        return 0;
    }

    let mut base: i64 = 0;
    let mut best: i64 = 0;
    let mut first: bool = true;

    let mut i: usize = 0;
    while i < n {
        let nr = nuts[i][0];
        let nc = nuts[i][1];

        let dt = abs_diff(tr, nr) + abs_diff(tc, nc);
        let ds = abs_diff(sr, nr) + abs_diff(sc, nc);

        base = base + 2 * dt;

        let candidate = ds - dt;
        if first {
            best = candidate;
            first = false;
        } else if candidate < best {
            best = candidate;
        }

        i += 1;
    }

    base + best
}
