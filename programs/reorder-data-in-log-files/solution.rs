fn first_space(s: &[u8]) -> usize {
    let mut i: usize = 0;
    let mut result: usize = s.len();
    let mut found: bool = false;
    while i < s.len() && !found {
        if s[i] == b' ' {
            result = i;
            found = true;
        }
        i += 1;
    }
    result
}

fn copy_bytes(s: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len() {
        out.push(s[i]);
        i += 1;
    }
    out
}

// Returns -1 if a < b, 1 if a > b, 0 if equal, comparing first by
// content (after identifier) then by identifier. No early returns.
fn cmp_letter(a: &[u8], b: &[u8]) -> i64 {
    let pa: usize = first_space(a);
    let pb: usize = first_space(b);

    let mut cmp: i64 = 0;

    // Compare contents
    let mut i: usize = pa + 1;
    let mut j: usize = pb + 1;
    while cmp == 0 && i < a.len() && j < b.len() {
        if a[i] < b[j] {
            cmp = -1;
        } else if a[i] > b[j] {
            cmp = 1;
        }
        i += 1;
        j += 1;
    }
    if cmp == 0 {
        if i < a.len() {
            cmp = 1;
        } else if j < b.len() {
            cmp = -1;
        }
    }

    // If contents equal, compare identifiers
    if cmp == 0 {
        let mut k: usize = 0;
        let mut l: usize = 0;
        while cmp == 0 && k < pa && l < pb {
            if a[k] < b[l] {
                cmp = -1;
            } else if a[k] > b[l] {
                cmp = 1;
            }
            k += 1;
            l += 1;
        }
        if cmp == 0 {
            if k < pa {
                cmp = 1;
            } else if l < pb {
                cmp = -1;
            }
        }
    }

    cmp
}

pub fn reorder_log_files(logs: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut letters: Vec<Vec<u8>> = Vec::new();
    let mut digits: Vec<Vec<u8>> = Vec::new();

    let mut idx: usize = 0;
    while idx < logs.len() {
        let row: &[u8] = &logs[idx];
        let p: usize = first_space(row);
        let c: u8 = row[p + 1];

        if c >= b'0' && c <= b'9' {
            digits.push(copy_bytes(row));
        } else {
            letters.push(copy_bytes(row));
        }

        idx += 1;
    }

    let n: usize = letters.len();

    // Index array 0..n
    let mut order: Vec<usize> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        order.push(t);
        t += 1;
    }

    // Insertion sort of indices using manual swaps, comparing letter logs.
    let mut i: usize = 1;
    while i < n {
        let mut j: usize = i;
        while j > 0 {
            let a: &[u8] = &letters[order[j]];
            let b: &[u8] = &letters[order[j - 1]];
            let c: i64 = cmp_letter(a, b);
            if c < 0 {
                let tmp: usize = order[j];
                order[j] = order[j - 1];
                order[j - 1] = tmp;
                j -= 1;
            } else {
                j = 0;
            }
        }
        i += 1;
    }

    let mut out: Vec<Vec<u8>> = Vec::new();

    let mut k: usize = 0;
    while k < n {
        out.push(copy_bytes(&letters[order[k]]));
        k += 1;
    }

    k = 0;
    while k < digits.len() {
        out.push(copy_bytes(&digits[k]));
        k += 1;
    }

    out
}
