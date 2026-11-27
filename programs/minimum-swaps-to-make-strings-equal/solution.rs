pub fn minimum_swap(s1: &[u8], s2: &[u8]) -> i64 {
    let n = s1.len();
    let mut xy: i64 = 0;
    let mut yx: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if s1[i] == b'x' && s2[i] == b'y' {
            xy += 1;
        } else if s1[i] == b'y' && s2[i] == b'x' {
            yx += 1;
        }
        i += 1;
    }

    if (xy + yx) % 2 != 0 {
        return -1;
    }

    xy / 2 + yx / 2 + (xy % 2) * 2
}
