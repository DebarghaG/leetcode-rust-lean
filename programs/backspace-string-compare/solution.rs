pub fn backspace_compare(s: &[u8], t: &[u8]) -> bool {
    let mut rs: Vec<u8> = Vec::new();
    let mut ls: usize = 0;
    let mut i: usize = 0;
    while i < s.len() {
        if s[i] == b'#' {
            if ls > 0 {
                ls -= 1;
            }
        } else {
            if ls < rs.len() {
                rs[ls] = s[i];
            } else {
                rs.push(s[i]);
            }
            ls += 1;
        }
        i += 1;
    }

    let mut rt: Vec<u8> = Vec::new();
    let mut lt: usize = 0;
    let mut j: usize = 0;
    while j < t.len() {
        if t[j] == b'#' {
            if lt > 0 {
                lt -= 1;
            }
        } else {
            if lt < rt.len() {
                rt[lt] = t[j];
            } else {
                rt.push(t[j]);
            }
            lt += 1;
        }
        j += 1;
    }

    let mut equal: bool = true;
    if ls != lt {
        equal = false;
    } else {
        let mut k: usize = 0;
        while k < ls {
            if rs[k] != rt[k] {
                equal = false;
            }
            k += 1;
        }
    }
    equal
}
