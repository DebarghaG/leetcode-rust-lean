pub fn max_distance(colors: &[i64]) -> i64 {
    let n = colors.len();
    let ni = n as i64;
    let mut best: i64 = 0;
    let mut i: i64 = 0;

    while i < ni {
        let mut j: i64 = i + 1;
        while j < ni {
            if colors[i as usize] != colors[j as usize] {
                let d: i64 = j - i;
                if d > best {
                    best = d;
                }
            }
            j += 1;
        }
        i += 1;
    }

    best
}
