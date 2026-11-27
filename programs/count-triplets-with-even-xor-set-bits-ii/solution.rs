fn odd_popcount(mut x: i64) -> bool {
    let mut odd = false;
    while x != 0 {
        odd = !odd;
        x = x & (x - 1);
    }
    odd
}

pub fn triplet_count(a: &[i64], b: &[i64], c: &[i64]) -> i64 {
    let mut a_even: i64 = 0;
    let mut a_odd: i64 = 0;
    let mut b_even: i64 = 0;
    let mut b_odd: i64 = 0;
    let mut c_even: i64 = 0;
    let mut c_odd: i64 = 0;

    let mut i: usize = 0;
    while i < a.len() {
        if odd_popcount(a[i]) {
            a_odd += 1;
        } else {
            a_even += 1;
        }
        i += 1;
    }

    i = 0;
    while i < b.len() {
        if odd_popcount(b[i]) {
            b_odd += 1;
        } else {
            b_even += 1;
        }
        i += 1;
    }

    i = 0;
    while i < c.len() {
        if odd_popcount(c[i]) {
            c_odd += 1;
        } else {
            c_even += 1;
        }
        i += 1;
    }

    let mut ans: i64 = 0;
    ans += a_even * b_even * c_even;
    ans += a_even * b_odd * c_odd;
    ans += a_odd * b_even * c_odd;
    ans += a_odd * b_odd * c_even;

    ans
}
