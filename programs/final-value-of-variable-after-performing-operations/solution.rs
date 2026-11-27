pub fn final_value_after_operations(operations: &[Vec<u8>]) -> i64 {
    let mut x: i64 = 0;
    let mut i: usize = 0;

    while i < operations.len() {
        let op = &operations[i];
        if op[1] == b'+' {
            x += 1;
        } else {
            x -= 1;
        }
        i += 1;
    }

    x
}
