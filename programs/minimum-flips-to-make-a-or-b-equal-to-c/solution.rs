pub fn min_flips(a: i64, b: i64, c: i64) -> i64 {
    let mut aa = a;
    let mut bb = b;
    let mut cc = c;
    let mut flips = 0;

    while aa > 0 || bb > 0 || cc > 0 {
        let abit = aa % 2;
        let bbit = bb % 2;
        let cbit = cc % 2;

        if cbit == 1 {
            if abit == 0 && bbit == 0 {
                flips += 1;
            }
        } else {
            if abit == 1 {
                flips += 1;
            }
            if bbit == 1 {
                flips += 1;
            }
        }

        aa /= 2;
        bb /= 2;
        cc /= 2;
    }

    flips
}
