pub fn min_number_operations(target: &[i64]) -> i64 {
    let n: usize = target.len();
    if n == 0 {
        return 0;
    }

    let mut ops: i64 = target[0];
    let mut i: usize = 1;
    while i < n {
        if target[i] > target[i - 1] {
            ops += target[i] - target[i - 1];
        }
        i += 1;
    }
    ops
}
