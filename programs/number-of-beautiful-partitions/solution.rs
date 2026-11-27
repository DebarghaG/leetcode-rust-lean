fn is_prime_digit(c: u8) -> bool {
    c == b'2' || c == b'3' || c == b'5' || c == b'7'
}

pub fn beautiful_partitions(s: &[u8], k: i64, minLength: i64) -> i64 {
    let n: usize = s.len();
    let kk: usize = k as usize;
    let l: usize = minLength as usize;
    let modulo: i64 = 1000000007;

    let mut prev: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        prev.push(0);
        i += 1;
    }
    prev[0] = 1;

    let mut p: usize = 1;
    while p <= kk {
        let mut curr: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z <= n {
            curr.push(0);
            z += 1;
        }

        let mut running: i64 = 0;
        let mut idx: usize = 1;

        while idx <= n {
            if idx >= l {
                let j: usize = idx - l;
                if j < n && is_prime_digit(s[j]) {
                    running = running + prev[j];
                    running = running % modulo;
                }
            }

            if !is_prime_digit(s[idx - 1]) {
                curr[idx] = running;
            } else {
                curr[idx] = 0;
            }

            idx += 1;
        }

        let mut c: usize = 0;
        while c <= n {
            prev[c] = curr[c];
            c += 1;
        }

        p += 1;
    }

    prev[n] % modulo
}
