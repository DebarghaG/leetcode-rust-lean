pub fn find_anagrams(s: &[u8], p: &[u8]) -> Vec<i64> {
    let n = s.len();
    let m = p.len();
    let mut result: Vec<i64> = Vec::new();

    if m > n {
        return result;
    }

    let mut need: Vec<i64> = Vec::new();
    let mut window: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < 26 {
        need.push(0);
        window.push(0);
        i += 1;
    }

    i = 0;
    while i < m {
        let idx = (p[i] - b'a') as usize;
        need[idx] += 1;
        i += 1;
    }

    i = 0;
    while i < m {
        let idx = (s[i] - b'a') as usize;
        window[idx] += 1;
        i += 1;
    }

    let mut start: usize = 0;
    while start + m <= n {
        let mut ok: bool = true;
        let mut k: usize = 0;

        while k < 26 {
            if need[k] != window[k] {
                ok = false;
                break;
            }
            k += 1;
        }

        if ok {
            result.push(start as i64);
        }

        if start + m < n {
            let old_idx = (s[start] - b'a') as usize;
            window[old_idx] -= 1;

            let new_idx = (s[start + m] - b'a') as usize;
            window[new_idx] += 1;
        }

        start += 1;
    }

    result
}
