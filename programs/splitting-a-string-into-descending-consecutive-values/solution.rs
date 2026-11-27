fn dec(canon: &[u8]) -> Vec<u8> {
    let len = canon.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < len {
        out.push(canon[i]);
        i += 1;
    }
    let mut j = len;
    let mut borrow: u8 = 1;
    while j > 0 && borrow == 1 {
        j -= 1;
        let d = out[j] - b'0';
        if d >= 1 {
            out[j] = b'0' + (d - 1);
            borrow = 0;
        } else {
            out[j] = b'9';
            borrow = 1;
        }
    }
    let mut start = 0;
    while start < out.len() && out[start] == b'0' {
        start += 1;
    }
    if start == out.len() {
        let mut res: Vec<u8> = Vec::new();
        res.push(b'0');
        res
    } else {
        let mut res: Vec<u8> = Vec::new();
        let mut k = start;
        while k < out.len() {
            res.push(out[k]);
            k += 1;
        }
        res
    }
}

fn check_from(s: &[u8], first_len: usize) -> bool {
    let n = s.len();
    let mut sig_start = 0;
    while sig_start < first_len && s[sig_start] == b'0' {
        sig_start += 1;
    }
    let mut prev_canon: Vec<u8> = Vec::new();
    if sig_start == first_len {
        prev_canon.push(b'0');
    } else {
        let mut i = sig_start;
        while i < first_len {
            prev_canon.push(s[i]);
            i += 1;
        }
    }
    let mut pos = first_len;
    let mut valid = true;
    let mut done = false;
    while pos < n && valid && !done {
        let is_zero = prev_canon.len() == 1 && prev_canon[0] == b'0';
        if is_zero {
            valid = false;
        } else {
            let target = dec(&prev_canon);
            let target_is_zero = target.len() == 1 && target[0] == b'0';
            if target_is_zero {
                let mut all_zeros = true;
                let mut q = pos;
                while q < n {
                    if s[q] != b'0' {
                        all_zeros = false;
                    }
                    q += 1;
                }
                if all_zeros {
                    done = true;
                } else {
                    valid = false;
                }
            } else {
                let mut z = 0;
                while pos + z < n && s[pos + z] == b'0' {
                    z += 1;
                }
                let mut match_ok = true;
                let mut t = 0;
                while t < target.len() {
                    let idx = pos + z + t;
                    if idx >= n {
                        match_ok = false;
                    } else {
                        if s[idx] != target[t] {
                            match_ok = false;
                        }
                    }
                    t += 1;
                }
                if match_ok {
                    pos = pos + z + target.len();
                    prev_canon = target;
                } else {
                    valid = false;
                }
            }
        }
    }
    valid && (done || pos == n)
}

pub fn split_string(s: &[u8]) -> bool {
    let n = s.len();
    if n < 2 {
        return false;
    }
    let mut found = false;
    let mut first_len = 1;
    while first_len < n && !found {
        if check_from(s, first_len) {
            found = true;
        }
        first_len += 1;
    }
    found
}
