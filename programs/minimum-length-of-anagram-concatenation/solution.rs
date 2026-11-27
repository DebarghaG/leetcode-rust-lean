pub fn min_anagram_length(s: &[u8]) -> i64 {
    let n: usize = s.len();
    if n == 0 {
        return 0;
    }

    let mut base: Vec<i64> = Vec::new();
    let mut cur: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c < 26 {
        base.push(0);
        cur.push(0);
        c += 1;
    }

    let mut k: usize = 1;
    while k <= n {
        if n % k == 0 {
            let mut z: usize = 0;
            while z < 26 {
                base[z] = 0;
                z += 1;
            }

            let mut i: usize = 0;
            while i < k {
                let idx: usize = (s[i] - b'a') as usize;
                base[idx] += 1;
                i += 1;
            }

            let mut ok: bool = true;
            let mut start: usize = k;

            while start < n && ok {
                z = 0;
                while z < 26 {
                    cur[z] = 0;
                    z += 1;
                }

                let mut j: usize = 0;
                while j < k {
                    let idx: usize = (s[start + j] - b'a') as usize;
                    cur[idx] += 1;
                    j += 1;
                }

                z = 0;
                while z < 26 {
                    if base[z] != cur[z] {
                        ok = false;
                    }
                    z += 1;
                }

                start += k;
            }

            if ok {
                return k as i64;
            }
        }

        k += 1;
    }

    n as i64
}
