fn trailing_zeroes(x: i64) -> i64 {
    let mut n = x;
    let mut count: i64 = 0;
    while n > 0 {
        n = n / 5;
        count += n;
    }
    count
}

pub fn preimage_size_fzf(k: i64) -> i64 {
    let mut lo: i64 = 0;
    let mut hi: i64 = 5 * k;

    while lo < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        if trailing_zeroes(mid) >= k {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    if trailing_zeroes(lo) == k {
        5
    } else {
        0
    }
}
