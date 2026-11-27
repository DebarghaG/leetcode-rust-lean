pub fn reinitialize_permutation(n: i64) -> i64 {
    let half: i64 = n / 2;
    let mut cur: i64 = 1;
    let mut ops: i64 = 0;

    loop {
        if cur < half {
            cur = cur * 2;
        } else {
            cur = (cur - half) * 2 + 1;
        }

        ops += 1;

        if cur == 1 {
            break;
        }
    }

    ops
}
