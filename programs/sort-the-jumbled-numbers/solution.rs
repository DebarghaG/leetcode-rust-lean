fn mapped_value(mapping: &[i64], x0: i64) -> i64 {
    if x0 == 0 {
        return mapping[0];
    }

    let mut x = x0;
    let mut res: i64 = 0;
    let mut place: i64 = 1;

    while x > 0 {
        let d = (x % 10) as usize;
        res = res + mapping[d] * place;
        place = place * 10;
        x = x / 10;
    }

    res
}

pub fn sort_jumbled(mapping: &[i64], nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut keys: Vec<i64> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let x = nums[i];
        keys.push(mapped_value(mapping, x));
        vals.push(x);
        i += 1;
    }

    if n <= 1 {
        return vals;
    }

    let mut tmp_keys: Vec<i64> = Vec::new();
    let mut tmp_vals: Vec<i64> = Vec::new();

    let mut t = 0;
    while t < n {
        tmp_keys.push(0);
        tmp_vals.push(0);
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

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if keys[a] <= keys[b] {
                    tmp_keys[k] = keys[a];
                    tmp_vals[k] = vals[a];
                    a += 1;
                } else {
                    tmp_keys[k] = keys[b];
                    tmp_vals[k] = vals[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                tmp_keys[k] = keys[a];
                tmp_vals[k] = vals[a];
                a += 1;
                k += 1;
            }

            while b < right {
                tmp_keys[k] = keys[b];
                tmp_vals[k] = vals[b];
                b += 1;
                k += 1;
            }

            left = left + width + width;
        }

        let mut q = 0;
        while q < n {
            keys[q] = tmp_keys[q];
            vals[q] = tmp_vals[q];
            q += 1;
        }

        width = width * 2;
    }

    vals
}
