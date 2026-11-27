pub fn maximum_length(s: &[u8]) -> i64 {
    let n = s.len();
    let mut best: i64 = -1;
    let mut c: u8 = b'a';

    while c <= b'z' {
        let mut k: usize = 1;
        while k <= n {
            let mut total: i64 = 0;
            let mut i: usize = 0;

            while i < n {
                if s[i] == c {
                    let start: usize = i;
                    while i < n && s[i] == c {
                        i += 1;
                    }
                    let len: usize = i - start;
                    if len >= k {
                        total += (len - k + 1) as i64;
                    }
                } else {
                    i += 1;
                }
            }

            if total >= 3 && (k as i64) > best {
                best = k as i64;
            }

            k += 1;
        }

        c += 1;
    }

    best
}
