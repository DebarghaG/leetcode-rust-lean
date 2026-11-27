pub fn does_valid_array_exist(derived: &[i64]) -> bool {
    let n = derived.len();
    let mut parity = false;
    let mut i = 0;

    while i < n {
        if derived[i] != 0 {
            parity = !parity;
        }
        i += 1;
    }

    !parity
}
