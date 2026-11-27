pub fn largest_overlap(img1: &[Vec<i64>], img2: &[Vec<i64>]) -> i64 {
    let n = img1.len();
    if n == 0 {
        return 0;
    }

    let shifts = 2 * n - 1;
    let mut best: i64 = 0;

    let mut vr: usize = 0;
    while vr < shifts {
        let mut a: usize = 0;
        let mut b: usize = 0;
        let mut rows: usize = 0;

        if vr < n {
            a = 0;
            b = vr;
            rows = n - vr;
        } else {
            a = vr - n + 1;
            b = 0;
            rows = n - a;
        }

        let mut hc: usize = 0;
        while hc < shifts {
            let mut c: usize = 0;
            let mut d: usize = 0;
            let mut cols: usize = 0;

            if hc < n {
                c = 0;
                d = hc;
                cols = n - hc;
            } else {
                c = hc - n + 1;
                d = 0;
                cols = n - c;
            }

            let mut count: i64 = 0;
            let mut i: usize = 0;
            while i < rows {
                let mut j: usize = 0;
                while j < cols {
                    if img1[a + i][c + j] == 1 && img2[b + i][d + j] == 1 {
                        count += 1;
                    }
                    j += 1;
                }
                i += 1;
            }

            if count > best {
                best = count;
            }

            hc += 1;
        }

        vr += 1;
    }

    best
}
