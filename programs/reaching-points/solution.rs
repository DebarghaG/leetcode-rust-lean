pub fn reaching_points(sx: i64, sy: i64, tx: i64, ty: i64) -> bool {
    let mut x = tx;
    let mut y = ty;

    while x >= sx && y >= sy {
        if x == sx && y == sy {
            return true;
        }

        if x > y {
            if y == sy {
                return (x - sx) % y == 0;
            }
            x = x % y;
        } else {
            if x == sx {
                return (y - sy) % x == 0;
            }
            y = y % x;
        }
    }

    false
}
