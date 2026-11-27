pub fn mirror_reflection(p: i64, q: i64) -> i64 {
    let mut a = p;
    let mut b = q;

    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }

    let g = a;
    let reduced_p = p / g;
    let reduced_q = q / g;

    if reduced_p % 2 == 0 {
        return 2;
    }
    if reduced_q % 2 == 0 {
        return 0;
    }
    1
}
