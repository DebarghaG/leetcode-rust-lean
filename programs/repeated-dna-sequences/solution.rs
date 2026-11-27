fn dna_val(c: u8) -> i64 {
    if c == b'A' {
        0
    } else if c == b'C' {
        1
    } else if c == b'G' {
        2
    } else {
        3
    }
}

pub fn find_repeated_dna_sequences(s: &[u8]) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let n: usize = s.len();
    if n < 10 {
        return out;
    }
    let limit: usize = n - 10;

    let mut all_codes: Vec<i64> = Vec::new();
    let mut sorted_codes: Vec<i64> = Vec::new();

    let mut code: i64 = 0;
    let mut j: usize = 0;
    while j < 10 {
        code = code * 4 + dna_val(s[j]);
        j += 1;
    }
    all_codes.push(code);
    sorted_codes.push(code);

    let mut i: usize = 1;
    while i <= limit {
        let old_v: i64 = dna_val(s[i - 1]);
        let new_v: i64 = dna_val(s[i + 9]);
        code = (code - old_v * 262144) * 4 + new_v;
        all_codes.push(code);
        sorted_codes.push(code);
        i += 1;
    }

    sorted_codes.sort();

    let m: usize = sorted_codes.len();
    let mut dups: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < m {
        let mut j2: usize = idx + 1;
        while j2 < m && sorted_codes[j2] == sorted_codes[idx] {
            j2 += 1;
        }
        if j2 - idx > 1 {
            dups.push(sorted_codes[idx]);
        }
        idx = j2;
    }

    let d: usize = dups.len();
    if d == 0 {
        return out;
    }

    let mut used: Vec<bool> = Vec::new();
    let mut u: usize = 0;
    while u < d {
        used.push(false);
        u += 1;
    }

    let total: usize = all_codes.len();
    let mut w: usize = 0;
    while w < total {
        let cur: i64 = all_codes[w];

        let mut lo: usize = 0;
        let mut hi: usize = d;
        let mut found: usize = d;
        while lo < hi {
            let mid: usize = (lo + hi) / 2;
            if dups[mid] == cur {
                found = mid;
                break;
            } else if dups[mid] < cur {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if found < d {
            if !used[found] {
                used[found] = true;

                let mut row: Vec<u8> = Vec::new();
                let mut k: usize = 0;
                while k < 10 {
                    row.push(b'A');
                    k += 1;
                }

                let mut val: i64 = cur;
                let mut pos: usize = 10;
                while pos > 0 {
                    pos -= 1;
                    let digit: i64 = val % 4;
                    let b: u8 = if digit == 0 {
                        b'A'
                    } else if digit == 1 {
                        b'C'
                    } else if digit == 2 {
                        b'G'
                    } else {
                        b'T'
                    };
                    row[pos] = b;
                    val = val / 4;
                }

                out.push(row);
            }
        }

        w += 1;
    }

    out
}
