pub fn max_substring_length(s: &[u8], k: i64) -> bool {
    if k == 0 {
        return true;
    }

    let n = s.len();

    let mut first: Vec<i64> = Vec::new();
    let mut last: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < 26 {
        first.push(-1);
        last.push(-1);
        i += 1;
    }

    i = 0;
    while i < n {
        let code = s[i] as usize;
        let idx = code - 97;
        if first[idx] == -1 {
            first[idx] = i as i64;
        }
        last[idx] = i as i64;
        i += 1;
    }

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut c: usize = 0;
    while c < 26 {
        if first[c] >= 0 {
            let mut l = first[c];
            let mut r = last[c];
            let mut changed = true;

            while changed {
                changed = false;
                let mut pos = l;
                while pos <= r {
                    let code = s[pos as usize] as usize;
                    let idx = code - 97;

                    if first[idx] < l {
                        l = first[idx];
                        changed = true;
                    }
                    if last[idx] > r {
                        r = last[idx];
                        changed = true;
                    }

                    pos += 1;
                }
            }

            if l != 0 || r != (n as i64) - 1 {
                starts.push(l);
                ends.push(r);
            }
        }
        c += 1;
    }

    let m = starts.len();

    i = 0;
    while i < m {
        let mut best = i;
        let mut j = i + 1;

        while j < m {
            if ends[j] < ends[best] {
                best = j;
            } else if ends[j] == ends[best] && starts[j] < starts[best] {
                best = j;
            }
            j += 1;
        }

        if best != i {
            let tmp_start = starts[i];
            starts[i] = starts[best];
            starts[best] = tmp_start;

            let tmp_end = ends[i];
            ends[i] = ends[best];
            ends[best] = tmp_end;
        }

        i += 1;
    }

    let mut count: i64 = 0;
    let mut last_end: i64 = -1;

    i = 0;
    while i < m {
        if starts[i] > last_end {
            count += 1;
            last_end = ends[i];
        }
        i += 1;
    }

    count >= k
}
