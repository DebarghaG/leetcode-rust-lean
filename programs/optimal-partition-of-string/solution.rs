pub fn partition_string(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut seen: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        seen.push(false);
        k += 1;
    }

    let mut count: i64 = 1;
    let mut i: usize = 0;

    while i < n {
        let idx: usize = (s[i] - b'a') as usize;

        if seen[idx] {
            count += 1;

            let mut j: usize = 0;
            while j < 26 {
                seen[j] = false;
                j += 1;
            }
        }

        seen[idx] = true;
        i += 1;
    }

    count
}
