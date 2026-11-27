pub fn min_subarray(nums: &[i64], p: i64) -> i64 {
    let n = nums.len();

    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);

    let mut i = 0;
    while i < n {
        let cur = pref[i];
        let val = nums[i] % p;
        let next = (cur + val) % p;
        pref.push(next);
        i += 1;
    }

    let target = pref[n];
    if target == 0 {
        return 0;
    }

    let m = (n as i64) + 1;
    let mut encoded: Vec<i64> = Vec::new();

    let mut k = 0;
    while k <= n {
        encoded.push(pref[k] * m + (k as i64));
        k += 1;
    }

    // Bottom-up merge sort of encoded values.
    let len = encoded.len();
    let mut temp: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < len {
        temp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < len {
        let mut start: usize = 0;

        while start < len {
            let mut mid = start + width;
            if mid > len {
                mid = len;
            }

            let mut end = mid + width;
            if end > len {
                end = len;
            }

            let mut left = start;
            let mut right = mid;
            let mut out = start;

            while left < mid && right < end {
                if encoded[left] <= encoded[right] {
                    temp[out] = encoded[left];
                    left += 1;
                } else {
                    temp[out] = encoded[right];
                    right += 1;
                }
                out += 1;
            }

            while left < mid {
                temp[out] = encoded[left];
                left += 1;
                out += 1;
            }

            while right < end {
                temp[out] = encoded[right];
                right += 1;
                out += 1;
            }

            start = end;
        }

        let mut c = 0;
        while c < len {
            encoded[c] = temp[c];
            c += 1;
        }

        width = width * 2;
    }

    let mut best: i64 = (n as i64) + 1;
    let mut j: usize = 1;

    while j <= n {
        let pj = pref[j];

        let mut r = pj - target;
        if r < 0 {
            r += p;
        }

        let rbase = r * m;
        let bound = rbase + (j as i64) - 1;

        let mut lo: usize = 0;
        let mut hi: usize = len;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if encoded[mid] <= bound {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        if lo > 0 {
            let key = encoded[lo - 1];

            if key >= rbase && key < rbase + m {
                let cand = key - rbase;

                // Removing nums[0..n] as a whole is not allowed.
                if !(j == n && cand == 0) {
                    let cur_len = (j as i64) - cand;
                    if cur_len < best {
                        best = cur_len;
                    }
                }
            }
        }

        j += 1;
    }

    if best > n as i64 {
        return -1;
    }

    best
}
