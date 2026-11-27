pub fn min_number_of_frogs(croakOfFrogs: &[u8]) -> i64 {
    let mut c: i64 = 0;
    let mut r: i64 = 0;
    let mut o: i64 = 0;
    let mut a: i64 = 0;

    let mut active: i64 = 0;
    let mut max_frogs: i64 = 0;

    let n = croakOfFrogs.len();
    let mut i: usize = 0;

    while i < n {
        let b = croakOfFrogs[i];

        if b == b'c' {
            c += 1;
            active += 1;
            if active > max_frogs {
                max_frogs = active;
            }
        } else if b == b'r' {
            if c == 0 {
                return -1;
            }
            c -= 1;
            r += 1;
        } else if b == b'o' {
            if r == 0 {
                return -1;
            }
            r -= 1;
            o += 1;
        } else if b == b'a' {
            if o == 0 {
                return -1;
            }
            o -= 1;
            a += 1;
        } else if b == b'k' {
            if a == 0 {
                return -1;
            }
            a -= 1;
            active -= 1;
        } else {
            return -1;
        }

        i += 1;
    }

    if c != 0 || r != 0 || o != 0 || a != 0 {
        return -1;
    }

    max_frogs
}
