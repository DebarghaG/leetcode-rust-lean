pub fn minimum_time_to_initial_state(word: &[u8], k: i64) -> i64 {
    let n: usize = word.len();
    if n == 0 {
        return 1;
    }

    let mut z: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        z.push(0);
        i += 1;
    }

    let mut l: usize = 0;
    let mut r: usize = 0;

    i = 1;
    while i < n {
        if i < r {
            let rem: usize = r - i;
            let val: usize = z[i - l] as usize;
            if val < rem {
                z[i] = val as i64;
            } else {
                z[i] = rem as i64;
            }
        }

        while i + (z[i] as usize) < n {
            let zi: usize = z[i] as usize;
            if word[zi] != word[i + zi] {
                break;
            }
            z[i] = z[i] + 1;
        }

        let end: usize = i + (z[i] as usize);
        if end > r {
            l = i;
            r = end;
        }

        i += 1;
    }

    let step: usize = k as usize;
    let mut t: usize = 1;
    let mut pos: usize = step;

    while pos < n {
        if z[pos] as usize >= n - pos {
            return t as i64;
        }
        t += 1;
        pos += step;
    }

    t as i64
}
