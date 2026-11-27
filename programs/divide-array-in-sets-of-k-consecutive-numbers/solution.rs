pub fn is_possible_divide(nums: &[i64], k: i64) -> bool {
    if k <= 0 {
        return false;
    }

    let n = nums.len();
    let kk = k as usize;

    if n == 0 {
        return true;
    }

    if n % kk != 0 {
        return false;
    }

    if kk == 1 {
        return true;
    }

    // Copy into an owned vector.
    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    // Manual insertion sort (avoids relying on std sort).
    let mut p = 1;
    while p < n {
        let key = a[p];
        let mut q = p;
        while q > 0 && a[q - 1] > key {
            a[q] = a[q - 1];
            q -= 1;
        }
        a[q] = key;
        p += 1;
    }

    // Compress into distinct values and their counts.
    let mut vals: Vec<i64> = Vec::new();
    let mut cnt: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        let v = a[i];
        let mut c: i64 = 0;
        while i < n && a[i] == v {
            c += 1;
            i += 1;
        }
        vals.push(v);
        cnt.push(c);
    }

    let m = vals.len();
    let mut ok = true;
    let mut d = 0;
    while d < m {
        if ok && cnt[d] > 0 {
            let c = cnt[d];
            if d + kk > m {
                ok = false;
            } else {
                let mut t = 0;
                while t < kk && ok {
                    let expected = vals[d] + (t as i64);
                    if vals[d + t] != expected {
                        ok = false;
                    } else if cnt[d + t] < c {
                        ok = false;
                    } else {
                        cnt[d + t] = cnt[d + t] - c;
                    }
                    t += 1;
                }
            }
        }
        d += 1;
    }

    ok
}
