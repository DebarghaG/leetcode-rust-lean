fn sort_vec(v: &mut Vec<i64>) {
    let n: usize = v.len();
    if n < 2 {
        return;
    }

    let mut temp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        temp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;

        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = left + width + width;
            if right > n {
                right = n;
            }

            let mut i: usize = left;
            let mut j: usize = mid;
            let mut t: usize = left;

            while i < mid && j < right {
                if v[i] <= v[j] {
                    temp[t] = v[i];
                    i += 1;
                } else {
                    temp[t] = v[j];
                    j += 1;
                }
                t += 1;
            }

            while i < mid {
                temp[t] = v[i];
                i += 1;
                t += 1;
            }

            while j < right {
                temp[t] = v[j];
                j += 1;
                t += 1;
            }

            left = left + width + width;
        }

        let mut p: usize = 0;
        while p < n {
            v[p] = temp[p];
            p += 1;
        }

        width = width + width;
    }
}

pub fn min_cost(arr: &[i64], brr: &[i64], k: i64) -> i64 {
    let n: usize = arr.len();

    let mut base: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut d = arr[i] - brr[i];
        if d < 0 {
            d = -d;
        }
        base += d;
        i += 1;
    }

    if base <= k {
        return base;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        a.push(arr[i]);
        b.push(brr[i]);
        i += 1;
    }

    sort_vec(&mut a);
    sort_vec(&mut b);

    let mut sorted_diff: i64 = 0;
    i = 0;
    while i < n {
        let mut d = a[i] - b[i];
        if d < 0 {
            d = -d;
        }
        sorted_diff += d;
        i += 1;
    }

    let rearranged_cost = k + sorted_diff;
    if rearranged_cost < base {
        rearranged_cost
    } else {
        base
    }
}
