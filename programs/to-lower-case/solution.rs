pub fn to_lower_case(s: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let n = s.len();
    let mut i: usize = 0;

    while i < n {
        let b = s[i];
        if b >= b'A' && b <= b'Z' {
            out.push(b + 32);
        } else {
            out.push(b);
        }
        i += 1;
    }

    out
}
