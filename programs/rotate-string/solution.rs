pub fn rotate_string(s: &[u8], goal: &[u8]) -> bool {
    let n = s.len();
    let m = goal.len();

    if n != m {
        return false;
    }

    if n == 0 {
        return true;
    }

    let mut shift: usize = 0;
    while shift < n {
        let mut j: usize = 0;
        let mut idx: usize = shift;
        let mut ok: bool = true;

        while j < n {
            if s[idx] != goal[j] {
                ok = false;
                j = n;
            } else {
                j += 1;
                idx += 1;
                if idx == n {
                    idx = 0;
                }
            }
        }

        if ok {
            return true;
        }

        shift += 1;
    }

    false
}
