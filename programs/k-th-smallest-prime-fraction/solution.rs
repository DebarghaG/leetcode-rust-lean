fn fraction_le(a: i64, b: i64, arr: &[i64], n: i64) -> bool {
    let i1 = (a / n) as usize;
    let j1 = (a % n) as usize;
    let i2 = (b / n) as usize;
    let j2 = (b % n) as usize;
    arr[i1] * arr[j2] <= arr[i2] * arr[j1]
}

pub fn kth_smallest_prime_fraction(arr: &[i64], k: i64) -> Vec<i64> {
    let n_usize = arr.len();
    let n = n_usize as i64;

    let mut vals: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        let mut j: usize = i + 1;
        while j < n_usize {
            let code = (i as i64) * n + (j as i64);
            vals.push(code);
            j += 1;
        }
        i += 1;
    }

    let total = vals.len();
    let mut aux: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < total {
        aux.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < total {
        let mut left: usize = 0;
        while left < total {
            let mid = if left + width < total { left + width } else { total };
            let right = if left + 2 * width < total { left + 2 * width } else { total };

            let mut p = left;
            let mut q = mid;
            let mut out = left;

            while p < mid && q < right {
                if fraction_le(vals[p], vals[q], arr, n) {
                    aux[out] = vals[p];
                    p += 1;
                } else {
                    aux[out] = vals[q];
                    q += 1;
                }
                out += 1;
            }

            while p < mid {
                aux[out] = vals[p];
                p += 1;
                out += 1;
            }

            while q < right {
                aux[out] = vals[q];
                q += 1;
                out += 1;
            }

            left += 2 * width;
        }

        t = 0;
        while t < total {
            vals[t] = aux[t];
            t += 1;
        }

        width *= 2;
    }

    let idx = (k - 1) as usize;
    let code = vals[idx];
    let i_idx = (code / n) as usize;
    let j_idx = (code % n) as usize;

    let mut ans: Vec<i64> = Vec::new();
    ans.push(arr[i_idx]);
    ans.push(arr[j_idx]);
    ans
}
