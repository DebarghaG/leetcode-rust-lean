fn can_form(sweetness: &[i64], pieces: i64, target: i64) -> bool {
    let n = sweetness.len();
    let mut count: i64 = 0;
    let mut current: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        current += sweetness[i];

        if current >= target {
            count += 1;
            if count >= pieces {
                return true;
            }
            current = 0;
        }

        i += 1;
    }

    false
}

pub fn maximize_sweetness(sweetness: &[i64], k: i64) -> i64 {
    let pieces = k + 1;
    let n = sweetness.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += sweetness[i];
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = total + 1;

    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;

        if can_form(sweetness, pieces, mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }

    lo
}
