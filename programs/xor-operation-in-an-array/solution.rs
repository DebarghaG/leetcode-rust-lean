pub fn xor_operation(n: i64, start: i64) -> i64 {
    let mut result: i64 = 0;
    let mut i: i64 = 0;

    while i < n {
        let value: i64 = start + 2 * i;
        result = result ^ value;
        i += 1;
    }

    result
}
