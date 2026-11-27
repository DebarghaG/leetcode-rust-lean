pub fn has_same_digits(s: &[u8]) -> bool {
    let n = s.len();
    if n < 2 {
        return true;
    }

    let k: usize = n - 2;

    let mut r: i64 = 1;
    let mut e2: i64 = 0;
    let mut e5: i64 = 0;

    let mut a: i64 = 0;
    let mut b: i64 = 0;

    let mut i: usize = 0;
    while i <= k {
        let mut c: i64 = 0;
        if e5 > 0 {
            if e2 > 0 {
                c = 0;
            } else {
                c = (5 * r) % 10;
            }
        } else {
            let mut p: i64 = 1;
            if e2 > 0 {
                let rem = e2 % 4;
                if rem == 0 {
                    p = 6;
                } else if rem == 1 {
                    p = 2;
                } else if rem == 2 {
                    p = 4;
                } else {
                    p = 8;
                }
            }
            c = (r * p) % 10;
        }

        let d0: i64 = (s[i] - b'0') as i64;
        let d1: i64 = (s[i + 1] - b'0') as i64;

        a = (a + c * d0) % 10;
        b = (b + c * d1) % 10;

        if i < k {
            let mut num: i64 = (k - i) as i64;
            let mut den: i64 = (i + 1) as i64;

            while num % 2 == 0 {
                num = num / 2;
                e2 = e2 + 1;
            }
            while num % 5 == 0 {
                num = num / 5;
                e5 = e5 + 1;
            }

            r = (r * (num % 10)) % 10;

            while den % 2 == 0 {
                den = den / 2;
                e2 = e2 - 1;
            }
            while den % 5 == 0 {
                den = den / 5;
                e5 = e5 - 1;
            }

            let u: i64 = den % 10;
            let mut inv: i64 = 1;
            if u == 3 {
                inv = 7;
            } else if u == 7 {
                inv = 3;
            } else if u == 9 {
                inv = 9;
            }

            r = (r * inv) % 10;
        }

        i += 1;
    }

    a == b
}
