pub fn longest_palindrome(s: &[u8]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 128 {
        counts.push(0);
        i += 1;
    }

    let mut j: usize = 0;
    while j < s.len() {
        let idx: usize = s[j] as usize;
        counts[idx] = counts[idx] + 1;
        j += 1;
    }

    let mut length: i64 = 0;
    let mut has_odd: bool = false;

    let mut k: usize = 0;
    while k < 128 {
        let c: i64 = counts[k];
        if c % 2 == 0 {
            length = length + c;
        } else {
            length = length + c - 1;
            has_odd = true;
        }
        k += 1;
    }

    if has_odd {
        length = length + 1;
    }

    length
}
