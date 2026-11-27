pub fn count_points(rings: &[u8]) -> i64 {
    let mut masks: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 10 {
        masks.push(0);
        k += 1;
    }

    let mut i: usize = 0;
    while i + 1 < rings.len() {
        let color = rings[i];
        let rod = (rings[i + 1] - b'0') as usize;

        let mut bit: i64 = 0;
        if color == b'R' {
            bit = 1;
        } else if color == b'G' {
            bit = 2;
        } else if color == b'B' {
            bit = 4;
        }

        masks[rod] = masks[rod] | bit;
        i += 2;
    }

    let mut ans: i64 = 0;
    let mut r: usize = 0;
    while r < 10 {
        if masks[r] == 7 {
            ans += 1;
        }
        r += 1;
    }

    ans
}
