fn merge_sort_i64(v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    let mut a = v;
    if n <= 1 {
        return a;
    }

    let mut b: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        b.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }

            let mut right = left + width + width;
            if right > n {
                right = n;
            }

            let mut i = left;
            let mut j = mid;
            let mut p = left;

            while i < mid && j < right {
                if a[i] <= a[j] {
                    b[p] = a[i];
                    i += 1;
                } else {
                    b[p] = a[j];
                    j += 1;
                }
                p += 1;
            }

            while i < mid {
                b[p] = a[i];
                i += 1;
                p += 1;
            }

            while j < right {
                b[p] = a[j];
                j += 1;
                p += 1;
            }

            left += width + width;
        }

        let mut q: usize = 0;
        while q < n {
            a[q] = b[q];
            q += 1;
        }

        width = width + width;
    }

    a
}

pub fn max_path_length(coordinates: &[Vec<i64>], k: i64) -> i64 {
    let n = coordinates.len();
    let ki = k as usize;
    let kx = coordinates[ki][0];
    let ky = coordinates[ki][1];

    let max_y: i64 = 1_000_000_000;
    let m: i64 = 1_000_000_001;

    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let x = coordinates[i][0];
        let y = coordinates[i][1];
        let rem = max_y - y;
        let key = x * m + rem;
        keys.push(key);
        i += 1;
    }

    let keys = merge_sort_i64(keys);

    let mut tails_low: Vec<i64> = Vec::new();
    let mut tails_high: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < n {
        let key = keys[idx];
        let x = key / m;
        let rem = key % m;
        let y = max_y - rem;

        if x < kx && y < ky {
            let mut lo: usize = 0;
            let mut hi: usize = tails_low.len();

            while lo < hi {
                let mid = (lo + hi) / 2;
                if tails_low[mid] < y {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            }

            if lo == tails_low.len() {
                tails_low.push(y);
            } else {
                tails_low[lo] = y;
            }
        }

        if x > kx && y > ky {
            let mut lo: usize = 0;
            let mut hi: usize = tails_high.len();

            while lo < hi {
                let mid = (lo + hi) / 2;
                if tails_high[mid] < y {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            }

            if lo == tails_high.len() {
                tails_high.push(y);
            } else {
                tails_high[lo] = y;
            }
        }

        idx += 1;
    }

    1 + (tails_low.len() as i64) + (tails_high.len() as i64)
}
