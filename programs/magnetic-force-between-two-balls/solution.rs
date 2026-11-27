pub fn max_distance(position: &[i64], m: i64) -> i64 {
    let n = position.len();
    if n == 0 {
        return 0;
    }

    let mut pos: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        pos.push(position[i]);
        i += 1;
    }
    pos.sort();

    let mut lo: i64 = 0;
    let mut hi: i64 = pos[n - 1] - pos[0];

    while lo < hi {
        let mid: i64 = lo + (hi - lo + 1) / 2;
        if can_place(&pos, m, mid) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}

fn can_place(pos: &[i64], m: i64, dist: i64) -> bool {
    if pos.len() == 0 {
        return m <= 0;
    }

    let mut placed: i64 = 1;
    let mut last: i64 = pos[0];
    let mut i: usize = 1;

    while i < pos.len() {
        if pos[i] - last >= dist {
            placed += 1;
            last = pos[i];
            if placed >= m {
                return true;
            }
        }
        i += 1;
    }

    placed >= m
}
