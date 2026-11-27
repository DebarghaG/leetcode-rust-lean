pub fn min_knight_moves(x: i64, y: i64) -> i64 {
    let mut a: i64 = x;
    let mut b: i64 = y;

    if a < 0 {
        a = -a;
    }
    if b < 0 {
        b = -b;
    }

    if a < b {
        let tmp: i64 = a;
        a = b;
        b = tmp;
    }

    if a == 1 && b == 0 {
        return 3;
    }
    if a == 2 && b == 2 {
        return 4;
    }

    let mut d: i64 = (a + 1) / 2;
    let s: i64 = (a + b + 2) / 3;
    if s > d {
        d = s;
    }

    if (d + a + b) % 2 != 0 {
        d = d + 1;
    }

    d
}
