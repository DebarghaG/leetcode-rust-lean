fn min2(a: usize, b: usize) -> usize {
    if a < b {
        a
    } else {
        b
    }
}

pub fn minimum_abs_difference(arr: &[i64]) -> Vec<Vec<i64>> {
    let n = arr.len();

    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        a.push(arr[idx]);
        idx += 1;
    }

    let mut tmp: Vec<i64> = Vec::new();
    idx = 0;
    while idx < n {
        tmp.push(0);
        idx += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid = min2(left + width, n);
            let right = min2(left + 2 * width, n);

            let mut i = left;
            let mut j = mid;
            let mut k = left;

            while i < mid && j < right {
                if a[i] <= a[j] {
                    tmp[k] = a[i];
                    i += 1;
                } else {
                    tmp[k] = a[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                tmp[k] = a[i];
                i += 1;
                k += 1;
            }

            while j < right {
                tmp[k] = a[j];
                j += 1;
                k += 1;
            }

            left += 2 * width;
        }

        idx = 0;
        while idx < n {
            a[idx] = tmp[idx];
            idx += 1;
        }

        width = width * 2;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();

    if n < 2 {
        return out;
    }

    let mut min_diff: i64 = a[1] - a[0];
    idx = 0;
    while idx + 1 < n {
        let d = a[idx + 1] - a[idx];
        if d < min_diff {
            min_diff = d;
        }
        idx += 1;
    }

    idx = 0;
    while idx + 1 < n {
        if a[idx + 1] - a[idx] == min_diff {
            let mut pair: Vec<i64> = Vec::new();
            pair.push(a[idx]);
            pair.push(a[idx + 1]);
            out.push(pair);
        }
        idx += 1;
    }

    out
}
