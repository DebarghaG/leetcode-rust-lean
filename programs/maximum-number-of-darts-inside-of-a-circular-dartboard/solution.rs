fn compare_sq_times(a: i64, d: i64, b: i64, k: i64) -> i64 {
    let base: i64 = 1_000_000_000;

    let a0 = a % base;
    let a1 = a / base;
    let p0 = a0 * a0;
    let c0 = p0 % base;
    let carry0 = p0 / base;
    let cross = 2 * a0 * a1 + carry0;
    let c1 = cross % base;
    let carry1 = cross / base;
    let c2 = a1 * a1 + carry1;

    let t0 = c0 * d;
    let l0 = t0 % base;
    let mut carry = t0 / base;
    let t1 = c1 * d + carry;
    let l1 = t1 % base;
    carry = t1 / base;
    let t2 = c2 * d + carry;
    let l2 = t2 % base;
    let l3 = t2 / base;

    let b0 = b % base;
    let b1 = b / base;
    let q0 = b0 * b0;
    let r0 = q0 % base;
    let carryr0 = q0 / base;
    let crossr = 2 * b0 * b1 + carryr0;
    let r1 = crossr % base;
    let carryr1 = crossr / base;
    let r2c = b1 * b1 + carryr1;

    let u0 = r0 * k;
    let rr0 = u0 % base;
    let mut carryr = u0 / base;
    let u1 = r1 * k + carryr;
    let rr1 = u1 % base;
    carryr = u1 / base;
    let u2 = r2c * k + carryr;
    let rr2 = u2 % base;
    let rr3 = u2 / base;

    if l3 != rr3 {
        if l3 < rr3 {
            return -1;
        } else {
            return 1;
        }
    }
    if l2 != rr2 {
        if l2 < rr2 {
            return -1;
        } else {
            return 1;
        }
    }
    if l1 != rr1 {
        if l1 < rr1 {
            return -1;
        } else {
            return 1;
        }
    }
    if l0 != rr0 {
        if l0 < rr0 {
            return -1;
        } else {
            return 1;
        }
    }
    0
}

fn le_irrational(a: i64, d: i64, b: i64, k: i64) -> bool {
    if k == 0 {
        return a <= 0;
    }
    if a == 0 {
        return b >= 0;
    }
    if b == 0 {
        return a <= 0;
    }

    if a > 0 {
        if b < 0 {
            return false;
        }
        return compare_sq_times(a, d, b, k) <= 0;
    } else {
        if b > 0 {
            return true;
        }
        let aa = -a;
        let bb = -b;
        return compare_sq_times(aa, d, bb, k) >= 0;
    }
}

pub fn num_points(darts: &[Vec<i64>], r: i64) -> i64 {
    let n = darts.len();
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let mut ans: i64 = 1;
    let four_r2 = 4 * r * r;

    let mut i: usize = 0;
    while i < n {
        let xi = darts[i][0];
        let yi = darts[i][1];

        let mut j: usize = i + 1;
        while j < n {
            let xj = darts[j][0];
            let yj = darts[j][1];

            let dx = xj - xi;
            let dy = yj - yi;
            let d2 = dx * dx + dy * dy;

            if d2 <= four_r2 {
                let k = four_r2 - d2;

                let mut t: usize = 0;
                while t < 2 {
                    let s: i64 = if t == 0 { -1 } else { 1 };
                    let mut cnt: i64 = 0;

                    let mut p: usize = 0;
                    while p < n {
                        let px = darts[p][0];
                        let py = darts[p][1];

                        let ux = 2 * px - xi - xj;
                        let uy = 2 * py - yi - yj;

                        let e = ux * ux + uy * uy - d2;
                        let w = -ux * dy + uy * dx;
                        let bcoef = 2 * s * w;

                        if le_irrational(e, d2, bcoef, k) {
                            cnt += 1;
                        }

                        p += 1;
                    }

                    if cnt > ans {
                        ans = cnt;
                    }

                    t += 1;
                }
            }

            j += 1;
        }

        i += 1;
    }

    ans
}
