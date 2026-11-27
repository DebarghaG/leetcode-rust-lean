pub fn make_strings_equal(s: &[u8], target: &[u8]) -> bool {
    let mut s_has_one: bool = false;
    let mut target_has_one: bool = false;

    let mut i: usize = 0;
    while i < s.len() {
        if s[i] == b'1' {
            s_has_one = true;
        }
        i += 1;
    }

    let mut j: usize = 0;
    while j < target.len() {
        if target[j] == b'1' {
            target_has_one = true;
        }
        j += 1;
    }

    s_has_one == target_has_one
}
