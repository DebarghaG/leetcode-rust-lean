pub fn check_inclusion(s1: &[u8], s2: &[u8]) -> bool {
    let n1 = s1.len();
    let n2 = s2.len();

    if n1 > n2 {
        return false;
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
    while i < n1 {
        let idx: usize = (s1[i] - b'a') as usize;
        need[idx] = need[idx] + 1;
        i += 1;
    }

    i = 0;
    while i < n1 {
        let idx: usize = (s2[i] - b'a') as usize;
        window[idx] = window[idx] + 1;
        i += 1;
    }

    let mut equal = true;
    i = 0;
    while i < 26 {
        if need[i] != window[i] {
            equal = false;
        }
        i += 1;
    }

    if equal {
        return true;
    }

    let mut right: usize = n1;
    while right < n2 {
        let add_idx: usize = (s2[right] - b'a') as usize;
        window[add_idx] = window[add_idx] + 1;

        let remove_idx: usize = (s2[right - n1] - b'a') as usize;
        window[remove_idx] = window[remove_idx] - 1;

        let mut same = true;
        i = 0;
        while i < 26 {
            if need[i] != window[i] {
                same = false;
            }
            i += 1;
        }

        if same {
            return true;
        }

        right += 1;
    }

    false
}
