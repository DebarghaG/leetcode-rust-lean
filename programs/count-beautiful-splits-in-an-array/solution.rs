fn z_values(nums: &[i64], start: usize) -> Vec<i64> {
    let n = nums.len();
    let m = n - start;
    let mut z: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < m {
        z.push(0);
        k += 1;
    }

    if m == 0 {
        return z;
    }

    z[0] = m as i64;

    let mut l: usize = 0;
    let mut r: usize = 0;
    let mut i: usize = 1;

    while i < m {
        let mut len: usize = 0;

        if i < r {
            let v = z[i - l] as usize;
            let rem = r - i;
            if v < rem {
                len = v;
            } else {
                len = rem;
            }
        }

        while i + len < m && nums[start + i + len] == nums[start + len] {
            len += 1;
        }

        z[i] = len as i64;

        if i + len > r {
            l = i;
            r = i + len;
        }

        i += 1;
    }

    z
}

pub fn beautiful_splits(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n < 3 {
        return 0;
    }

    let global_z = z_values(nums, 0);
    let mut count: i64 = 0;

    let mut i: usize = 1;
    while i + 1 < n {
        let m = n - i;
        let z = z_values(nums, i);
        let a_active = global_z[i] >= i as i64;

        let mut d: usize = 1;
        while d < m {
            let mut ok = false;

            if a_active && d >= i {
                ok = true;
            }

            if !ok && d <= m - d && z[d] >= d as i64 {
                ok = true;
            }

            if ok {
                count += 1;
            }

            d += 1;
        }

        i += 1;
    }

    count
}
