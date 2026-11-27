pub fn max_score(prices: &[i64]) -> i64 {
    let n = prices.len();
    if n == 0 {
        return 0;
    }

    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        keys.push(prices[i] - (i as i64));
        i += 1;
    }

    let mut temp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        temp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right = if left + width * 2 < n { left + width * 2 } else { n };

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if keys[a] <= keys[b] {
                    temp[k] = keys[a];
                    a += 1;
                } else {
                    temp[k] = keys[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                temp[k] = keys[a];
                a += 1;
                k += 1;
            }

            while b < right {
                temp[k] = keys[b];
                b += 1;
                k += 1;
            }

            left += width * 2;
        }

        let mut j: usize = 0;
        while j < n {
            keys[j] = temp[j];
            j += 1;
        }

        width = width * 2;
    }

    let mut uniq: Vec<i64> = Vec::new();
    let mut sums: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < n {
        let key = keys[idx];
        if uniq.len() == 0 || uniq[uniq.len() - 1] != key {
            uniq.push(key);
            sums.push(0);
        }
        idx += 1;
    }

    let m = uniq.len();
    let mut p: usize = 0;
    while p < n {
        let key = prices[p] - (p as i64);

        let mut lo: usize = 0;
        let mut hi: usize = m;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if uniq[mid] < key {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        sums[lo] += prices[p];
        p += 1;
    }

    let mut ans: i64 = sums[0];
    let mut q: usize = 1;
    while q < m {
        if sums[q] > ans {
            ans = sums[q];
        }
        q += 1;
    }

    ans
}
