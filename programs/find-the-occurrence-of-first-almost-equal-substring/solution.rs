fn z_function(a: &[u8]) -> Vec<usize> {
    let n = a.len();
    let mut z: Vec<usize> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        z.push(0);
        t += 1;
    }

    if n == 0 {
        return z;
    }

    z[0] = n;

    let mut l: usize = 0;
    let mut r: usize = 0;
    let mut i: usize = 1;

    while i < n {
        if i < r {
            let mut v = z[i - l];
            let max_v = r - i;
            if v > max_v {
                v = max_v;
            }
            z[i] = v;
        }

        let mut j = z[i];
        while i + j < n && a[j] == a[i + j] {
            j += 1;
        }
        z[i] = j;

        if i + j > r {
            l = i;
            r = i + j;
        }

        i += 1;
    }

    z
}

pub fn min_starting_index(s: &[u8], pattern: &[u8]) -> i64 {
    let n = s.len();
    let m = pattern.len();

    if m == 0 {
        return 0;
    }
    if m > n {
        return -1;
    }

    let mut combined: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        combined.push(pattern[i]);
        i += 1;
    }
    combined.push(0u8);
    i = 0;
    while i < n {
        combined.push(s[i]);
        i += 1;
    }

    let z_forward = z_function(&combined);

    let mut rev_combined: Vec<u8> = Vec::new();
    i = 0;
    while i < m {
        rev_combined.push(pattern[m - 1 - i]);
        i += 1;
    }
    rev_combined.push(0u8);
    i = 0;
    while i < n {
        rev_combined.push(s[n - 1 - i]);
        i += 1;
    }

    let z_reverse = z_function(&rev_combined);

    let offset: usize = m + 1;
    let mut start: usize = 0;
    let mut result: i64 = -1;
    let mut done: bool = false;

    while start + m <= n && !done {
        let prefix_len = z_forward[offset + start];
        let mut ok: bool = false;

        if prefix_len >= m {
            ok = true;
        } else {
            let tail_len = m - prefix_len - 1;
            if tail_len == 0 {
                ok = true;
            } else {
                let rev_start = n - (start + m);
                let rev_index = offset + rev_start;
                if z_reverse[rev_index] >= tail_len {
                    ok = true;
                }
            }
        }

        if ok {
            result = start as i64;
            done = true;
        } else {
            start += 1;
        }
    }

    result
}
