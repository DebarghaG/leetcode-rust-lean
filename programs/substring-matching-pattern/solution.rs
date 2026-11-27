pub fn has_match(s: &[u8], p: &[u8]) -> bool {
    let n = s.len();
    let m = p.len();

    let mut pos: usize = 0;
    let mut i: usize = 0;

    while i < m {
        if p[i] == b'*' {
            i += 1;
        } else {
            let start = i;
            while i < m && p[i] != b'*' {
                i += 1;
            }
            let len = i - start;

            let mut j = pos;
            let mut found = false;

            while j + len <= n {
                let mut k = 0;
                let mut ok = true;

                while k < len {
                    if s[j + k] != p[start + k] {
                        ok = false;
                        k = len;
                    } else {
                        k += 1;
                    }
                }

                if ok {
                    pos = j + len;
                    found = true;
                    j = n;
                } else {
                    j += 1;
                }
            }

            if !found {
                return false;
            }
        }
    }

    true
}
