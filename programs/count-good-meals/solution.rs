pub fn count_pairs(deliciousness: &[i64]) -> i64 {
    let modulo: i64 = 1000000007;
    let n = deliciousness.len();
    if n < 2 {
        return 0;
    }

    // Copy the input into an owned vector.
    let mut src: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        src.push(deliciousness[i]);
        i += 1;
    }

    // Scratch buffer for radix sort.
    let mut dst: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        dst.push(0);
        i += 1;
    }

    // Radix sort with two passes of 11 bits.
    let mut count: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c < 2048 {
        count.push(0);
        c += 1;
    }

    // Pass 1: sort by the lowest 11 bits into dst.
    c = 0;
    while c < 2048 {
        count[c] = 0;
        c += 1;
    }
    i = 0;
    while i < n {
        let d = ((src[i] & 2047) as usize);
        count[d] = count[d] + 1;
        i += 1;
    }
    let mut sum: i64 = 0;
    c = 0;
    while c < 2048 {
        let old = count[c];
        count[c] = sum;
        sum = sum + old;
        c += 1;
    }
    i = 0;
    while i < n {
        let d = ((src[i] & 2047) as usize);
        let pos = count[d] as usize;
        dst[pos] = src[i];
        count[d] = count[d] + 1;
        i += 1;
    }

    // Pass 2: sort by the next 11 bits from dst back into src.
    c = 0;
    while c < 2048 {
        count[c] = 0;
        c += 1;
    }
    i = 0;
    while i < n {
        let d = (((dst[i] >> 11) & 2047) as usize);
        count[d] = count[d] + 1;
        i += 1;
    }
    sum = 0;
    c = 0;
    while c < 2048 {
        let old = count[c];
        count[c] = sum;
        sum = sum + old;
        c += 1;
    }
    i = 0;
    while i < n {
        let d = (((dst[i] >> 11) & 2047) as usize);
        let pos = count[d] as usize;
        src[pos] = dst[i];
        count[d] = count[d] + 1;
        i += 1;
    }

    // Now src is sorted.
    let min_sum = src[0] + src[1];
    let max_sum = src[n - 2] + src[n - 1];

    let mut ans: i64 = 0;
    let mut p: i64 = 1;
    while p < min_sum {
        p = p * 2;
    }

    while p <= max_sum {
        let mut l: usize = 0;
        let mut r: usize = n - 1;

        while l < r {
            let s = src[l] + src[r];
            if s < p {
                l = l + 1;
            } else if s > p {
                r = r - 1;
            } else {
                let lv = src[l];
                let rv = src[r];

                if lv == rv {
                    let cnt = (r - l + 1) as i64;
                    ans = ans + cnt * (cnt - 1) / 2;
                    l = r;
                } else {
                    let mut lc: i64 = 0;
                    let mut ll = l;
                    while ll < n && src[ll] == lv {
                        lc = lc + 1;
                        ll = ll + 1;
                    }

                    let mut rc: i64 = 0;
                    let mut rr = r;
                    while rr > l && src[rr] == rv {
                        rc = rc + 1;
                        rr = rr - 1;
                    }

                    ans = ans + lc * rc;
                    l = l + (lc as usize);
                    r = r - (rc as usize);
                }
            }
        }

        p = p * 2;
    }

    ans % modulo
}
