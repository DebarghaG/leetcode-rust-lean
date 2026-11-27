pub fn has_all_codes(s: &[u8], k: i64) -> bool {
    let n = s.len();

    if k <= 0 {
        return true;
    }

    let kk = k as usize;

    if kk > n {
        return false;
    }

    let windows = n - kk + 1;
    let windows_i = windows as i64;

    // target = 2^k (k <= 20 in the given constraints, so this fits in i64)
    let mut target: i64 = 1;
    let mut p: i64 = 0;
    while p < k {
        target = target * 2;
        p += 1;
    }

    if windows_i < target {
        return false;
    }

    let tsz = target as usize;

    let mut seen: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < tsz {
        seen.push(false);
        i += 1;
    }

    // Compute the code for the first window.
    let mut code: usize = 0;
    let mut j: usize = 0;
    while j < kk {
        code = code * 2;
        if s[j] == b'1' {
            code += 1;
        }
        j += 1;
    }
    seen[code] = true;
    let mut distinct: i64 = 1;

    // high = 2^(k-1), the weight of the outgoing bit.
    let mut high: usize = 1;
    let mut q: usize = 1;
    while q < kk {
        high = high * 2;
        q += 1;
    }

    let mut start: usize = 1;
    while start < windows {
        let mut old_bit: usize = 0;
        if s[start - 1] == b'1' {
            old_bit = 1;
        }

        let mut new_bit: usize = 0;
        if s[start + kk - 1] == b'1' {
            new_bit = 1;
        }

        code = code - old_bit * high;
        code = code * 2 + new_bit;

        if !seen[code] {
            seen[code] = true;
            distinct += 1;
        }

        start += 1;
    }

    distinct == target
}
