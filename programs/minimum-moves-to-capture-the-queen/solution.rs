pub fn min_moves_to_capture_the_queen(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64) -> i64 {
    let mut rook_can = false;

    // Rook attacks along the same column a == e.
    if a == e {
        let mut blocked = false;
        if c == a {
            if (d > b && d < f) || (d < b && d > f) {
                blocked = true;
            }
        }
        if !blocked {
            rook_can = true;
        }
    }

    // Rook attacks along the same row b == f.
    if b == f {
        let mut blocked = false;
        if d == b {
            if (c > a && c < e) || (c < a && c > e) {
                blocked = true;
            }
        }
        if !blocked {
            rook_can = true;
        }
    }

    let mut bishop_can = false;

    // Bishop and queen are on the same diagonal.
    let diff_ce = if c > e { c - e } else { e - c };
    let diff_df = if d > f { d - f } else { f - d };

    if diff_ce == diff_df {
        let mut blocked = false;

        // Check whether the rook is on the same diagonal as the bishop and queen.
        let diff_ac = if a > c { a - c } else { c - a };
        let diff_bd = if b > d { b - d } else { d - b };

        if diff_ac == diff_bd {
            let between_ce = (a > c && a < e) || (a < c && a > e);
            let between_df = (b > d && b < f) || (b < d && b > f);

            if between_ce && between_df {
                blocked = true;
            }
        }

        if !blocked {
            bishop_can = true;
        }
    }

    if rook_can || bishop_can {
        1
    } else {
        2
    }
}
