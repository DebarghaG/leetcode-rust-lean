fn find_occurrences(text: &[u8], pat: &[u8]) -> Vec<i64> {
    let mut res: Vec<i64> = Vec::new();
    let n = text.len();
    let m = pat.len();

    if m == 0 {
        let mut idx: usize = 0;
        while idx <= n {
            res.push(idx as i64);
            idx += 1;
        }
        return res;
    }

    if m > n {
        return res;
    }

    let mut lps: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < m {
        lps.push(0);
        z += 1;
    }

    let mut len: usize = 0;
    let mut i: usize = 1;
    while i < m {
        if pat[i] == pat[len] {
            len += 1;
            lps[i] = len as i64;
            i += 1;
        } else {
            if len != 0 {
                len = lps[len - 1] as usize;
            } else {
                lps[i] = 0;
                i += 1;
            }
        }
    }

    let mut ti: usize = 0;
    let mut pj: usize = 0;
    while ti < n {
        if text[ti] == pat[pj] {
            ti += 1;
            pj += 1;
            if pj == m {
                res.push((ti - pj) as i64);
                pj = lps[pj - 1] as usize;
            }
        } else {
            if pj != 0 {
                pj = lps[pj - 1] as usize;
            } else {
                ti += 1;
            }
        }
    }

    res
}

pub fn beautiful_indices(s: &[u8], a: &[u8], b: &[u8], k: i64) -> Vec<i64> {
    let apos = find_occurrences(s, a);
    let bpos = find_occurrences(s, b);

    let mut out: Vec<i64> = Vec::new();

    let blen = bpos.len();
    let mut bi: usize = 0;
    let alen = apos.len();
    let mut ai: usize = 0;

    while ai < alen {
        let pos = apos[ai];
        let low = pos - k;
        let high = pos + k;

        while bi < blen && bpos[bi] < low {
            bi += 1;
        }

        if bi < blen && bpos[bi] <= high {
            out.push(pos);
        }

        ai += 1;
    }

    out
}
