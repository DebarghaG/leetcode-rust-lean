fn merge_sort(v: &[i64]) -> Vec<i64> {
    let n = v.len();
    let mut src: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        src.push(v[i]);
        i += 1;
    }

    if n <= 1 {
        return src;
    }

    let mut width: usize = 1;
    while width < n {
        let mut dst: Vec<i64> = Vec::new();
        let mut start: usize = 0;
        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }
            let mut end = start + 2 * width;
            if end > n {
                end = n;
            }

            let mut a = start;
            let mut b = mid;
            while a < mid && b < end {
                if src[a] <= src[b] {
                    dst.push(src[a]);
                    a += 1;
                } else {
                    dst.push(src[b]);
                    b += 1;
                }
            }
            while a < mid {
                dst.push(src[a]);
                a += 1;
            }
            while b < end {
                dst.push(src[b]);
                b += 1;
            }

            start = end;
        }
        src = dst;
        width = width * 2;
    }

    src
}

pub fn beautiful_substrings(s: &[u8], k: i64) -> i64 {
    let n = s.len();

    // Convert k to usize without using casts.
    let mut ku: usize = 0;
    let mut kk: i64 = k;
    while kk > 0 {
        ku += 1;
        kk -= 1;
    }

    // Find the minimal positive p such that p^2 is divisible by k.
    let mut p: usize = 1;
    while (p * p) % ku != 0 {
        p += 1;
    }
    let period: usize = 2 * p;

    // Prefix difference: number of vowels minus number of consonants.
    let mut diff: Vec<i64> = Vec::new();
    diff.push(0);
    let mut d: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let c = s[i];
        if c == b'a' || c == b'e' || c == b'i' || c == b'o' || c == b'u' {
            d += 1;
        } else {
            d -= 1;
        }
        diff.push(d);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut r: usize = 0;
    while r < period {
        let mut group: Vec<i64> = Vec::new();
        let mut j: usize = r;
        while j <= n {
            group.push(diff[j]);
            j += period;
        }

        let sorted = merge_sort(&group);
        let len = sorted.len();

        let mut idx: usize = 0;
        while idx < len {
            let val = sorted[idx];
            let mut cnt: i64 = 0;
            let mut t: usize = idx;
            while t < len && sorted[t] == val {
                cnt += 1;
                t += 1;
            }
            ans += cnt * (cnt - 1) / 2;
            idx = t;
        }

        r += 1;
    }

    ans
}
