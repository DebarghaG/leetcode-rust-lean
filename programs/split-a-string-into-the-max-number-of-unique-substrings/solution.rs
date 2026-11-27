fn substring_used(
    starts: &[usize],
    ends: &[usize],
    used_len: usize,
    s: &[u8],
    start: usize,
    end: usize,
) -> bool {
    let len = end - start;
    let mut i = 0usize;
    while i < used_len {
        let s2 = starts[i];
        let e2 = ends[i];
        if e2 - s2 == len {
            let mut j = 0usize;
            let mut same = true;
            while j < len {
                if s[s2 + j] != s[start + j] {
                    same = false;
                    break;
                }
                j += 1;
            }
            if same {
                return true;
            }
        }
        i += 1;
    }
    false
}

pub fn max_unique_split(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut best: usize = 0;

    let mut used_start: Vec<usize> = Vec::new();
    let mut used_end: Vec<usize> = Vec::new();
    let mut used_len: usize = 0;

    let mut st_pos: Vec<usize> = Vec::new();
    let mut st_next: Vec<usize> = Vec::new();
    let mut st_base: Vec<usize> = Vec::new();

    st_pos.push(0);
    st_next.push(1);
    st_base.push(0);
    let mut stack_len: usize = 1;

    while stack_len > 0 {
        let idx = stack_len - 1;
        let base = st_base[idx];

        if used_len > base {
            used_len = base;
        }

        let pos = st_pos[idx];

        // Even in the best case, splitting every remaining byte separately
        // cannot improve the current best answer.
        if used_len + (n - pos) <= best {
            stack_len -= 1;
            used_len = base;
            continue;
        }

        if pos == n {
            if used_len > best {
                best = used_len;
            }
            stack_len -= 1;
            used_len = base;
            continue;
        }

        let mut end = st_next[idx];
        let mut chosen = false;

        while end <= n {
            st_next[idx] = end + 1;

            // Upper bound if we choose s[pos..end].
            if used_len + 1 + (n - end) > best {
                if !substring_used(&used_start, &used_end, used_len, s, pos, end) {
                    if used_len < used_start.len() {
                        used_start[used_len] = pos;
                        used_end[used_len] = end;
                    } else {
                        used_start.push(pos);
                        used_end.push(end);
                    }

                    used_len += 1;
                    let new_base = used_len;

                    if stack_len < st_pos.len() {
                        st_pos[stack_len] = end;
                        st_next[stack_len] = end + 1;
                        st_base[stack_len] = new_base;
                    } else {
                        st_pos.push(end);
                        st_next.push(end + 1);
                        st_base.push(new_base);
                    }

                    stack_len += 1;
                    chosen = true;
                    break;
                }
            }

            end += 1;
        }

        if !chosen {
            stack_len -= 1;
            used_len = base;
        }
    }

    best as i64
}
