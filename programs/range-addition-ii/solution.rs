pub fn max_count(m: i64, n: i64, ops: &[Vec<i64>]) -> i64 {
    if ops.len() == 0 {
        return m * n;
    }

    let mut min_a: i64 = m;
    let mut min_b: i64 = n;
    let mut i: usize = 0;

    while i < ops.len() {
        let a: i64 = ops[i][0];
        let b: i64 = ops[i][1];

        if a < min_a {
            min_a = a;
        }
        if b < min_b {
            min_b = b;
        }

        i += 1;
    }

    min_a * min_b
}
