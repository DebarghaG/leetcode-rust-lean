pub fn letter_case_permutation(s: &[u8]) -> Vec<Vec<u8>> {
    let mut res: Vec<Vec<u8>> = Vec::new();
    let mut empty: Vec<u8> = Vec::new();
    res.push(empty);

    let n = s.len();
    let mut i = 0;
    while i < n {
        let c = s[i];
        let is_lower = c >= b'a' && c <= b'z';
        let is_upper = c >= b'A' && c <= b'Z';
        let is_letter = is_lower || is_upper;

        let mut next: Vec<Vec<u8>> = Vec::new();
        let m = res.len();
        let mut j = 0;
        while j < m {
            let len = res[j].len();

            if is_letter {
                // First keep the original character.
                let mut a: Vec<u8> = Vec::new();
                let mut k = 0;
                while k < len {
                    a.push(res[j][k]);
                    k += 1;
                }
                a.push(c);
                next.push(a);

                // Then add the opposite-case character.
                let flipped: u8 = if is_lower { c - 32 } else { c + 32 };
                let mut b: Vec<u8> = Vec::new();
                let mut k2 = 0;
                while k2 < len {
                    b.push(res[j][k2]);
                    k2 += 1;
                }
                b.push(flipped);
                next.push(b);
            } else {
                let mut v: Vec<u8> = Vec::new();
                let mut k = 0;
                while k < len {
                    v.push(res[j][k]);
                    k += 1;
                }
                v.push(c);
                next.push(v);
            }

            j += 1;
        }

        res = next;
        i += 1;
    }

    res
}
