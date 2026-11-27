fn sq_dist(a: &[i64], b: &[i64]) -> i64 {
    let dx = a[0] - b[0];
    let dy = a[1] - b[1];
    dx * dx + dy * dy
}

pub fn valid_square(p1: &[i64], p2: &[i64], p3: &[i64], p4: &[i64]) -> bool {
    let mut ds: Vec<i64> = Vec::new();
    ds.push(sq_dist(p1, p2));
    ds.push(sq_dist(p1, p3));
    ds.push(sq_dist(p1, p4));
    ds.push(sq_dist(p2, p3));
    ds.push(sq_dist(p2, p4));
    ds.push(sq_dist(p3, p4));

    let n = ds.len();
    let mut i: usize = 1;
    while i < n {
        let key = ds[i];
        let mut j: usize = i;
        let mut placing: bool = true;
        while j > 0 && placing {
            if ds[j - 1] > key {
                ds[j] = ds[j - 1];
                j -= 1;
            } else {
                placing = false;
            }
        }
        ds[j] = key;
        i += 1;
    }

    if ds[0] <= 0 {
        return false;
    }
    if ds[0] != ds[1] || ds[0] != ds[2] || ds[0] != ds[3] {
        return false;
    }
    if ds[4] != ds[5] {
        return false;
    }
    if ds[4] != ds[0] * 2 {
        return false;
    }

    true
}
