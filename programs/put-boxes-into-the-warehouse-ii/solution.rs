fn sort_i64(mut v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if n <= 1 {
        return v;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        tmp.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid: usize;
            if left + width < n {
                mid = left + width;
            } else {
                mid = n;
            }

            let right: usize;
            if left + width + width < n {
                right = left + width + width;
            } else {
                right = n;
            }

            let mut i: usize = left;
            let mut j: usize = mid;
            let mut k: usize = left;

            while i < mid && j < right {
                if v[i] <= v[j] {
                    tmp[k] = v[i];
                    i += 1;
                } else {
                    tmp[k] = v[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                tmp[k] = v[i];
                i += 1;
                k += 1;
            }

            while j < right {
                tmp[k] = v[j];
                j += 1;
                k += 1;
            }

            left = right;
        }

        let mut c: usize = 0;
        while c < n {
            v[c] = tmp[c];
            c += 1;
        }

        width = width + width;
    }

    v
}

pub fn max_boxes_in_warehouse(boxes: &[i64], warehouse: &[i64]) -> i64 {
    let n = warehouse.len();
    let m = boxes.len();

    if n == 0 {
        return 0;
    }
    if m == 0 {
        return 0;
    }

    let mut left_min: Vec<i64> = Vec::new();
    let mut cur: i64 = warehouse[0];
    let mut i: usize = 0;
    while i < n {
        if warehouse[i] < cur {
            cur = warehouse[i];
        }
        left_min.push(cur);
        i += 1;
    }

    let mut capacities: Vec<i64> = Vec::new();
    let mut suffix_min: i64 = warehouse[n - 1];
    let mut j: usize = n;
    while j > 0 {
        j -= 1;

        if warehouse[j] < suffix_min {
            suffix_min = warehouse[j];
        }

        let mut cap: i64 = left_min[j];
        if suffix_min > cap {
            cap = suffix_min;
        }
        capacities.push(cap);
    }

    let mut bs: Vec<i64> = Vec::new();
    let mut b: usize = 0;
    while b < m {
        bs.push(boxes[b]);
        b += 1;
    }

    let bs = sort_i64(bs);
    let capacities = sort_i64(capacities);

    let mut count: i64 = 0;
    let mut bi: usize = 0;
    let mut ci: usize = 0;

    while bi < bs.len() && ci < capacities.len() {
        if bs[bi] <= capacities[ci] {
            count += 1;
            bi += 1;
            ci += 1;
        } else {
            ci += 1;
        }
    }

    count
}
