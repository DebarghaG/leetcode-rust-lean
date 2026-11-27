pub fn is_long_pressed_name(name: &[u8], typed: &[u8]) -> bool {
    let mut i: usize = 0;
    let mut j: usize = 0;

    while j < typed.len() {
        if i < name.len() && typed[j] == name[i] {
            i += 1;
            j += 1;
        } else if j > 0 && typed[j] == typed[j - 1] {
            j += 1;
        } else {
            return false;
        }
    }

    i == name.len()
}
