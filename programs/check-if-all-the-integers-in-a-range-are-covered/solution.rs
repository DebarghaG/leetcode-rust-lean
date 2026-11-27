pub fn is_covered(ranges: &[Vec<i64>], left: i64, right: i64) -> bool {
    let mut x = left;

    while x <= right {
        let mut covered = false;
        let mut i = 0;

        while i < ranges.len() {
            let row = &ranges[i];
            if row[0] <= x && x <= row[1] {
                covered = true;
            }
            i += 1;
        }

        if !covered {
            return false;
        }

        if x == right {
            break;
        }
        x += 1;
    }

    true
}
