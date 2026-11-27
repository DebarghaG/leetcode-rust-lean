fn build_parents(enc: i64, width: usize, base: i64, ppow: &[i64], allow: &[bool]) -> Vec<i64> {
    // rows[k] = true iff partial parent encoding `k` (of current length) is valid
    let mut rows: Vec<bool> = Vec::new();
    rows.push(true);
    let mut pow: i64 = 1; // = base^i, current length of partial encodings
    let mut i: usize = 0;
    let steps = width - 1;
    while i < steps {
        let new_size = pow * base;
        let mut new_rows: Vec<bool> = Vec::new();
        let mut t: i64 = 0;
        while t < new_size {
            new_rows.push(false);
            t = t + 1;
        }
        let a = (enc / ppow[width - 1 - i]) % base;
        let b = (enc / ppow[width - 2 - i]) % base;
        let mut k: i64 = 0;
        while k < new_size {
            let c = k % base;
            let p = k / base;
            let mut ok = false;
            if p >= 0 && p < pow {
                if rows[p as usize] {
                    let idx = (a * base + b) * base + c;
                    if idx >= 0 && (idx as usize) < allow.len() {
                        if allow[idx as usize] {
                            ok = true;
                        }
                    }
                }
            }
            if ok {
                new_rows[k as usize] = true;
            }
            k = k + 1;
        }
        rows = new_rows;
        pow = new_size;
        i = i + 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut j: i64 = 0;
    while j < pow {
        if rows[j as usize] {
            result.push(j);
        }
        j = j + 1;
    }
    result
}

pub fn pyramid_transition(bottom: &[u8], allowed: &[Vec<u8>]) -> bool {
    let n = bottom.len();

    // Dense symbol map (byte -> 0..base-1).
    let mut map: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < 256 {
        map.push(-1);
        z = z + 1;
    }
    let mut base: i64 = 0;

    let mut bi = 0;
    while bi < n {
        let b = bottom[bi] as usize;
        if map[b] == -1 {
            map[b] = base;
            base = base + 1;
        }
        bi = bi + 1;
    }
    let mut ai = 0;
    while ai < allowed.len() {
        let plen = allowed[ai].len();
        let mut q = 0;
        while q < plen {
            let b = allowed[ai][q] as usize;
            if map[b] == -1 {
                map[b] = base;
                base = base + 1;
            }
            q = q + 1;
        }
        ai = ai + 1;
    }

    // Flat allow table (size base^3).
    let allow_size = base * base * base;
    let mut allow: Vec<bool> = Vec::new();
    let mut s = 0;
    while s < allow_size {
        allow.push(false);
        s = s + 1;
    }
    let mut ai2 = 0;
    while ai2 < allowed.len() {
        let plen = allowed[ai2].len();
        if plen == 3 {
            let a = map[allowed[ai2][0] as usize];
            let b = map[allowed[ai2][1] as usize];
            let c = map[allowed[ai2][2] as usize];
            let idx = (a * base + b) * base + c;
            if idx >= 0 && (idx as usize) < allow.len() {
                allow[idx as usize] = true;
            }
        }
        ai2 = ai2 + 1;
    }

    // Powers of base: ppow[j] = base^j for j in 0..=n.
    let mut ppow: Vec<i64> = Vec::new();
    let mut pw: i64 = 1;
    let mut pi = 0;
    while pi <= n {
        ppow.push(pw);
        pw = pw * base;
        pi = pi + 1;
    }

    // Encode the bottom row.
    let mut start: i64 = 0;
    let mut ei = 0;
    while ei < n {
        let d = map[bottom[ei] as usize];
        start = start * base + d;
        ei = ei + 1;
    }

    // DP over levels.
    let mut width = n;
    let mut total = ppow[width];
    let mut mask: Vec<bool> = Vec::new();
    let mut m = 0;
    while m < total {
        mask.push(false);
        m = m + 1;
    }
    if start >= 0 && start < total {
        mask[start as usize] = true;
    }

    let mut level = 0;
    while level < n - 1 {
        let new_width = width - 1;
        let new_total = ppow[new_width];
        let mut new_mask: Vec<bool> = Vec::new();
        let mut m2 = 0;
        while m2 < new_total {
            new_mask.push(false);
            m2 = m2 + 1;
        }

        let mut any = false;
        let mut enc: i64 = 0;
        while enc < total {
            if mask[enc as usize] {
                let parents = build_parents(enc, width, base, &ppow, &allow);
                let mut pj = 0;
                while pj < parents.len() {
                    let v = parents[pj];
                    if v >= 0 && v < new_total {
                        new_mask[v as usize] = true;
                        any = true;
                    }
                    pj = pj + 1;
                }
            }
            enc = enc + 1;
        }

        if !any {
            return false;
        }

        mask = new_mask;
        total = new_total;
        width = new_width;
        level = level + 1;
    }

    true
}
