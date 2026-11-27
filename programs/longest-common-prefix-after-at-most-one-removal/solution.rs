pub fn longest_common_prefix(s: &[u8], t: &[u8]) -> i64 {
    let n = s.len();
    let m = t.len();

    let mut i: usize = 0;
    let mut prefix_ok: bool = true;

    while i < n && i < m && prefix_ok {
        if s[i] == t[i] {
            i += 1;
        } else {
            prefix_ok = false;
        }
    }

    if i == n || i == m {
        return i as i64;
    }

    let mut j: usize = i + 1;
    let mut k: usize = i;
    let mut matched: usize = 0;
    let mut suffix_ok: bool = true;

    while j < n && k < m && suffix_ok {
        if s[j] == t[k] {
            matched += 1;
            j += 1;
            k += 1;
        } else {
            suffix_ok = false;
        }
    }

    (i + matched) as i64
}
