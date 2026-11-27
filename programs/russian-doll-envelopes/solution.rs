pub fn max_envelopes(envelopes: &[Vec<i64>]) -> i64 {
    let n = envelopes.len();
    if n == 0 {
        return 0;
    }

    let base: i64 = 1000000;

    // Encode each envelope so that sorting the keys sorts by:
    // width ascending, and height descending for equal widths.
    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let w = envelopes[i][0];
        let h = envelopes[i][1];
        let key = w * base - h;
        keys.push(key);
        i += 1;
    }

    keys.sort();

    // Compute the strictly increasing LIS on the heights.
    let mut tails: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let key = keys[i];
        let rem = key % base;
        let h = base - rem;

        let mut lo: usize = 0;
        let mut hi: usize = tails.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            if tails[mid] < h {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo == tails.len() {
            tails.push(h);
        } else {
            tails[lo] = h;
        }

        i += 1;
    }

    tails.len() as i64
}
