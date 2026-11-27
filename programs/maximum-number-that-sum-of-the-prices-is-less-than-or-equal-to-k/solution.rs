fn accumulated_price(n: i64, x: i64) -> i64 {
    let total = n + 1;

    // bit = 2^(x - 1), the first selected bit position, 0-indexed.
    let mut bit: i64 = 1;
    let mut p: i64 = 0;
    while p < x - 1 {
        bit = bit * 2;
        p = p + 1;
    }

    // step = 2^x, the distance between selected bit positions.
    let mut step: i64 = 1;
    let mut q: i64 = 0;
    while q < x {
        step = step * 2;
        q = q + 1;
    }

    let mut sum: i64 = 0;

    while bit <= n {
        let cycle = bit * 2;
        let full = total / cycle;
        let rem = total % cycle;

        let mut cnt = full * bit;
        if rem > bit {
            cnt = cnt + (rem - bit);
        }

        sum = sum + cnt;
        bit = bit * step;
    }

    sum
}

pub fn find_maximum_number(k: i64, x: i64) -> i64 {
    let mut lo: i64 = 0;
    let mut hi: i64 = 10000000000000000;

    while lo < hi {
        let mid = lo + (hi - lo + 1) / 2;

        if accumulated_price(mid, x) <= k {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}
