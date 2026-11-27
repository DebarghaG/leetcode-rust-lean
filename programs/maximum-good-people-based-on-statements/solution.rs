pub fn maximum_good(statements: &[Vec<i64>]) -> i64 {
    let n: usize = statements.len();
    let limit: i64 = 1i64 << n;

    let mut best: i64 = 0;
    let mut mask: i64 = 0;

    while mask < limit {
        let mut ok: bool = true;
        let mut i: usize = 0;

        while i < n {
            if ((mask >> i) & 1i64) == 1i64 {
                let mut j: usize = 0;

                while j < n {
                    let s: i64 = statements[i][j];

                    if s != 2 {
                        let bit: i64 = (mask >> j) & 1i64;
                        if bit != s {
                            ok = false;
                        }
                    }

                    j += 1;
                }
            }

            i += 1;
        }

        if ok {
            let mut count: i64 = 0;
            let mut k: usize = 0;

            while k < n {
                count += (mask >> k) & 1i64;
                k += 1;
            }

            if count > best {
                best = count;
            }
        }

        mask += 1;
    }

    best
}
