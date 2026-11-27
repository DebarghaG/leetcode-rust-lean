pub fn count_pairs(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();
    if n < 2 {
        return 0;
    }

    let mut d: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        d.push(nums1[i] - nums2[i]);
        i += 1;
    }

    let mut buf: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        buf.push(0);
        i += 1;
    }

    // First radix pass: low 9 bits of (d + 100000).
    let mut counts: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c < 512 {
        counts.push(0);
        c += 1;
    }

    i = 0;
    while i < n {
        let val = d[i] + 100000;
        let digit = val & 511;
        let di = digit as usize;
        counts[di] = counts[di] + 1;
        i += 1;
    }

    let mut sum: i64 = 0;
    c = 0;
    while c < 512 {
        let cnt = counts[c];
        counts[c] = sum;
        sum += cnt;
        c += 1;
    }

    i = 0;
    while i < n {
        let val = d[i] + 100000;
        let digit = val & 511;
        let di = digit as usize;
        let pos = counts[di] as usize;
        buf[pos] = d[i];
        counts[di] = counts[di] + 1;
        i += 1;
    }

    i = 0;
    while i < n {
        d[i] = buf[i];
        i += 1;
    }

    // Second radix pass: next 9 bits.
    let mut counts2: Vec<i64> = Vec::new();
    c = 0;
    while c < 512 {
        counts2.push(0);
        c += 1;
    }

    i = 0;
    while i < n {
        let val = d[i] + 100000;
        let digit = (val >> 9) & 511;
        let di = digit as usize;
        counts2[di] = counts2[di] + 1;
        i += 1;
    }

    sum = 0;
    c = 0;
    while c < 512 {
        let cnt = counts2[c];
        counts2[c] = sum;
        sum += cnt;
        c += 1;
    }

    i = 0;
    while i < n {
        let val = d[i] + 100000;
        let digit = (val >> 9) & 511;
        let di = digit as usize;
        let pos = counts2[di] as usize;
        buf[pos] = d[i];
        counts2[di] = counts2[di] + 1;
        i += 1;
    }

    i = 0;
    while i < n {
        d[i] = buf[i];
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = n - 1;
    while left < right {
        if d[left] + d[right] > 0 {
            ans += (right - left) as i64;
            right -= 1;
        } else {
            left += 1;
        }
    }
    ans
}
