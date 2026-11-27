pub fn is_one_edit_distance(s: &[u8], t: &[u8]) -> bool {
    let n = s.len();
    let m = t.len();

    let mut diff: usize = 0;
    if n > m {
        diff = n - m;
    } else {
        diff = m - n;
    }
    if diff > 1 {
        return false;
    }

    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut edits: i64 = 0;

    while i < n && j < m {
        if s[i] == t[j] {
            i += 1;
            j += 1;
        } else {
            edits += 1;
            if n > m {
                i += 1;
            } else if m > n {
                j += 1;
            } else {
                i += 1;
                j += 1;
            }
        }
    }

    while i < n {
        edits += 1;
        i += 1;
    }

    while j < m {
        edits += 1;
        j += 1;
    }

    edits == 1
}
