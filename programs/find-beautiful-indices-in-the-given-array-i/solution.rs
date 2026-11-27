pub fn beautiful_indices(s: &[u8], a: &[u8], b: &[u8], k: i64) -> Vec<i64> {
    let n = s.len();
    let la = a.len();
    let lb = b.len();

    let mut occ_a: Vec<usize> = Vec::new();
    let mut occ_b: Vec<usize> = Vec::new();

    if la <= n {
        let last = n - la;
        let mut i: usize = 0;
        while i <= last {
            let mut ok = true;
            let mut j: usize = 0;
            while j < la && ok {
                if s[i + j] != a[j] {
                    ok = false;
                }
                j += 1;
            }
            if ok {
                occ_a.push(i);
            }
            i += 1;
        }
    }

    if lb <= n {
        let last = n - lb;
        let mut i: usize = 0;
        while i <= last {
            let mut ok = true;
            let mut j: usize = 0;
            while j < lb && ok {
                if s[i + j] != b[j] {
                    ok = false;
                }
                j += 1;
            }
            if ok {
                occ_b.push(i);
            }
            i += 1;
        }
    }

    let mut out: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    let mut idx: usize = 0;

    while idx < occ_a.len() {
        let ai = occ_a[idx];
        let ai_i = ai as i64;
        let lower = ai_i - k;

        while p < occ_b.len() && (occ_b[p] as i64) < lower {
            p += 1;
        }

        if p < occ_b.len() {
            let bi_i = occ_b[p] as i64;
            if bi_i <= ai_i + k {
                out.push(ai_i);
            }
        }

        idx += 1;
    }

    out
}
