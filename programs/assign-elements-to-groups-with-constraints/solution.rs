pub fn assign_elements(groups: &[i64], elements: &[i64]) -> Vec<i64> {
    let n = groups.len();
    if n == 0 {
        return Vec::new();
    }

    let mut max_g: usize = 0;
    let mut i: usize = 0;
    while i < n {
        let g = groups[i] as usize;
        if g > max_g {
            max_g = g;
        }
        i += 1;
    }

    let mut first: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= max_g {
        first.push(-1);
        k += 1;
    }

    let m = elements.len();
    let mut j: usize = 0;
    while j < m {
        let v = elements[j] as usize;
        if v <= max_g {
            if first[v] == -1 {
                first[v] = j as i64;
            }
        }
        j += 1;
    }

    let mut best: Vec<i64> = Vec::new();
    k = 0;
    while k <= max_g {
        best.push(-1);
        k += 1;
    }

    let mut v: usize = 1;
    while v <= max_g {
        let idx = first[v];
        if idx != -1 {
            let mut mult = v;
            while mult <= max_g {
                if best[mult] == -1 || idx < best[mult] {
                    best[mult] = idx;
                }
                mult += v;
            }
        }
        v += 1;
    }

    let mut out: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let g = groups[i] as usize;
        out.push(best[g]);
        i += 1;
    }

    out
}
