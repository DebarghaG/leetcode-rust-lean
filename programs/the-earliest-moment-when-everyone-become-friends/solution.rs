pub fn earliest_acq(logs: &[Vec<i64>], n: i64) -> i64 {
    let l = logs.len();

    // Build the initial order of log indices.
    let mut order: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < l {
        order.push(z as i64);
        z += 1;
    }

    // Temporary vector for iterative merge sort.
    let mut tmp: Vec<i64> = Vec::new();
    z = 0;
    while z < l {
        tmp.push(0);
        z += 1;
    }

    // Sort log indices by timestamp using bottom-up merge sort.
    let mut width: usize = 1;
    while width < l {
        let step = width * 2;
        let mut left: usize = 0;
        while left < l {
            let mid = if left + width < l { left + width } else { l };
            let right = if left + step < l { left + step } else { l };

            let mut i: usize = left;
            let mut j: usize = mid;
            let mut k: usize = left;

            while i < mid && j < right {
                let oi = order[i] as usize;
                let oj = order[j] as usize;
                if logs[oi][0] <= logs[oj][0] {
                    tmp[k] = order[i];
                    i += 1;
                } else {
                    tmp[k] = order[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                tmp[k] = order[i];
                i += 1;
                k += 1;
            }

            while j < right {
                tmp[k] = order[j];
                j += 1;
                k += 1;
            }

            let mut m: usize = left;
            while m < right {
                order[m] = tmp[m];
                m += 1;
            }

            left = left + step;
        }
        width = width * 2;
    }

    let nn = n as usize;
    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < nn {
        parent.push(idx as i64);
        size.push(1);
        idx += 1;
    }

    let mut components: i64 = n;
    if components <= 1 {
        return 0;
    }

    let mut p: usize = 0;
    while p < l {
        let row = &logs[order[p] as usize];
        let t = row[0];
        let x = row[1];
        let y = row[2];

        let mut rx = x;
        while parent[rx as usize] != rx {
            rx = parent[rx as usize];
        }

        let mut ry = y;
        while parent[ry as usize] != ry {
            ry = parent[ry as usize];
        }

        if rx != ry {
            let sx = size[rx as usize];
            let sy = size[ry as usize];

            if sx < sy {
                parent[rx as usize] = ry;
                size[ry as usize] = sx + sy;
            } else {
                parent[ry as usize] = rx;
                size[rx as usize] = sx + sy;
            }

            components -= 1;
            if components == 1 {
                return t;
            }
        }

        p += 1;
    }

    -1
}
