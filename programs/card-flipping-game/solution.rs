pub fn flipgame(fronts: &[i64], backs: &[i64]) -> i64 {
    let n = fronts.len();
    let mut x: i64 = 1;

    while x <= 2000 {
        let mut appears = false;
        let mut forbidden = false;
        let mut i: usize = 0;

        while i < n {
            if fronts[i] == x || backs[i] == x {
                appears = true;
            }
            if fronts[i] == x && backs[i] == x {
                forbidden = true;
            }
            i += 1;
        }

        if appears && !forbidden {
            return x;
        }

        x += 1;
    }

    0
}
