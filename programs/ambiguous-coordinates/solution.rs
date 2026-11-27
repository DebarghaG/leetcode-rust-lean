fn reps(s: &[u8], start: usize, end: usize) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();

    if start >= end {
        return out;
    }

    let len = end - start;

    // Decimal representations first, matching the usual expected order.
    let mut p: usize = 1;
    while p < len {
        let int_ok = p == 1 || s[start] != b'0';
        let frac_ok = s[end - 1] != b'0';

        if int_ok && frac_ok {
            let mut cur: Vec<u8> = Vec::new();
            let point = start + p;
            let mut i = start;
            while i < point {
                cur.push(s[i]);
                i = i + 1;
            }
            cur.push(b'.');
            i = point;
            while i < end {
                cur.push(s[i]);
                i = i + 1;
            }
            out.push(cur);
        }

        p = p + 1;
    }

    // Integer representation.
    if len == 1 || s[start] != b'0' {
        let mut cur: Vec<u8> = Vec::new();
        let mut i = start;
        while i < end {
            cur.push(s[i]);
            i = i + 1;
        }
        out.push(cur);
    }

    out
}

pub fn ambiguous_coordinates(s: &[u8]) -> Vec<Vec<u8>> {
    let mut res: Vec<Vec<u8>> = Vec::new();
    let n = s.len();

    if n < 3 {
        return res;
    }

    let mut k: usize = 2;
    while k <= n - 2 {
        let xs = reps(s, 1, k);
        let ys = reps(s, k, n - 1);

        let mut xi: usize = 0;
        while xi < xs.len() {
            let xlen = xs[xi].len();
            let mut yi: usize = 0;

            while yi < ys.len() {
                let ylen = ys[yi].len();
                let mut cur: Vec<u8> = Vec::new();

                cur.push(b'(');

                let mut i: usize = 0;
                while i < xlen {
                    cur.push(xs[xi][i]);
                    i = i + 1;
                }

                cur.push(b',');
                cur.push(b' ');

                i = 0;
                while i < ylen {
                    cur.push(ys[yi][i]);
                    i = i + 1;
                }

                cur.push(b')');
                res.push(cur);

                yi = yi + 1;
            }

            xi = xi + 1;
        }

        k = k + 1;
    }

    res
}
