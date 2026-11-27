pub fn nums_same_consec_diff(n: i64, k: i64) -> Vec<i64> {
    let mut cur: Vec<i64> = Vec::new();

    let mut d: i64 = 1;
    while d <= 9 {
        cur.push(d);
        d += 1;
    }

    let mut len: i64 = 1;
    while len < n {
        let mut next: Vec<i64> = Vec::new();

        let mut i: usize = 0;
        while i < cur.len() {
            let val = cur[i];
            let last = val % 10;

            let low = last - k;
            let high = last + k;

            if low >= 0 && low <= 9 {
                next.push(val * 10 + low);
            }

            if high >= 0 && high <= 9 && high != low {
                next.push(val * 10 + high);
            }

            i += 1;
        }

        cur = next;
        len += 1;
    }

    cur
}
