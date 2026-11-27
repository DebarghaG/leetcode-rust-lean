pub fn sum_scores(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut z: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        z.push(0);
        i += 1;
    }
    z[0] = n;

    let mut l: usize = 0;
    let mut r: usize = 0;
    let mut k: usize = 1;

    while k < n {
        if k <= r {
            let mut v: usize = r - k + 1;
            let other: usize = z[k - l];
            if other < v {
                v = other;
            }
            z[k] = v;
        }

        let mut zk: usize = z[k];
        let mut extending: bool = true;
        while extending {
            if k + zk >= n {
                extending = false;
            } else {
                if s[zk] == s[k + zk] {
                    zk += 1;
                } else {
                    extending = false;
                }
            }
        }
        z[k] = zk;

        if zk > 0 {
            let nr: usize = k + zk - 1;
            if nr > r {
                l = k;
                r = nr;
            }
        }

        k += 1;
    }

    let mut total: i64 = 0;
    let mut idx: usize = 0;
    while idx < n {
        total = total + (z[idx] as i64);
        idx += 1;
    }

    total
}
