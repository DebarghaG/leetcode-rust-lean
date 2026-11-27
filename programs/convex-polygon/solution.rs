pub fn is_convex(points: &[Vec<i64>]) -> bool {
    let n = points.len();
    if n < 3 {
        return true;
    }

    let mut sign: i64 = 0;
    let mut bad: bool = false;
    let mut i: usize = 0;

    while i < n {
        let mut j = i + 1;
        if j == n {
            j = 0;
        }

        let mut k = i + 2;
        if k >= n {
            k -= n;
        }

        let pi = &points[i];
        let pj = &points[j];
        let pk = &points[k];

        let cross = (pj[0] - pi[0]) * (pk[1] - pi[1])
            - (pj[1] - pi[1]) * (pk[0] - pi[0]);

        if cross > 0 {
            if sign < 0 {
                bad = true;
            } else {
                if sign == 0 {
                    sign = 1;
                }
            }
        } else {
            if cross < 0 {
                if sign > 0 {
                    bad = true;
                } else {
                    if sign == 0 {
                        sign = -1;
                    }
                }
            }
        }

        i += 1;
    }

    !bad
}
