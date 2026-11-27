pub fn min_flips(target: &[u8]) -> i64 {
    let mut flips: i64 = 0;
    let mut current: u8 = 0;
    let n = target.len();
    let mut i: usize = 0;

    while i < n {
        let bit: u8 = if target[i] == b'1' { 1 } else { 0 };

        if bit != current {
            flips += 1;
            if current == 0 {
                current = 1;
            } else {
                current = 0;
            }
        }

        i += 1;
    }

    flips
}
