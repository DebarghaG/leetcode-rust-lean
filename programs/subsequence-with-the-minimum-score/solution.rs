pub fn minimum_score(s: &[u8], t: &[u8]) -> i64 {
    let n: usize = s.len();
    let m: usize = t.len();

    // pre[l] = earliest ending position in s for the prefix t[0..l].
    // pre[0] = -1. If the prefix is impossible, store n as a sentinel.
    let mut pre: Vec<i64> = Vec::new();
    pre.push(-1);

    let mut p: usize = 0;
    let mut i: usize = 0;
    while i < m {
        while p < n && s[p] != t[i] {
            p += 1;
        }
        if p < n {
            pre.push(p as i64);
            p += 1;
        } else {
            pre.push(n as i64);
        }
        i += 1;
    }

    // If t itself is already a subsequence of s, no removal is needed.
    if pre[m] < n as i64 {
        return 0;
    }

    // suf[k] = latest possible first position in s for the suffix t[k..m].
    // suf[m] = n. If the suffix is impossible, store -1.
    let mut suf: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= m {
        suf.push(0);
        z += 1;
    }
    suf[m] = n as i64;

    let mut q: usize = n;
    let mut idx: usize = m;
    while idx > 0 {
        idx -= 1;

        let mut pos: usize = q;
        let mut found: bool = false;

        while pos > 0 && !found {
            pos -= 1;
            if s[pos] == t[idx] {
                found = true;
            }
        }

        if found {
            suf[idx] = pos as i64;
            q = pos;
        } else {
            suf[idx] = -1;
            q = 0;
        }
    }

    // Remove t[l..k-1], keeping t[0..l] and t[k..m].
    // This is possible iff pre[l] < suf[k].
    let mut best: i64 = m as i64;
    let mut k: usize = 1;
    let mut l: usize = 0;

    while l < m {
        if k < l + 1 {
            k = l + 1;
        }

        while k <= m && suf[k] <= pre[l] {
            k += 1;
        }

        if k <= m {
            let len: i64 = (k - l) as i64;
            if len < best {
                best = len;
            }
        }

        l += 1;
    }

    best
}
