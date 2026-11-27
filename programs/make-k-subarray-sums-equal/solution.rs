pub fn make_sub_k_sum_equal(arr: &[i64], k: i64) -> i64 {
    let n = arr.len();
    if n == 0 || k <= 0 {
        return 0;
    }

    let kk = k as usize;

    // Compute gcd(n, kk).
    let mut a = n;
    let mut b = kk;
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    let g = a;
    let cycle_len = n / g;

    let mut ans: i64 = 0;
    let mut start: usize = 0;

    while start < g {
        let mut vals: Vec<i64> = Vec::new();

        let mut idx = start;
        let mut t: usize = 0;
        while t < cycle_len {
            vals.push(arr[idx]);
            idx = (idx + kk) % n;
            t += 1;
        }

        // Find min and max in this cycle.
        let mut minv = vals[0];
        let mut maxv = vals[0];
        let mut j: usize = 1;
        while j < cycle_len {
            let v = vals[j];
            if v < minv {
                minv = v;
            }
            if v > maxv {
                maxv = v;
            }
            j += 1;
        }

        // Find the median by binary searching the value range.
        let target = cycle_len / 2 + 1;
        let mut lo = minv;
        let mut hi = maxv;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;

            let mut count: usize = 0;
            j = 0;
            while j < cycle_len {
                if vals[j] <= mid {
                    count += 1;
                }
                j += 1;
            }

            if count >= target {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        let median = lo;

        j = 0;
        while j < cycle_len {
            let v = vals[j];
            if v >= median {
                ans += v - median;
            } else {
                ans += median - v;
            }
            j += 1;
        }

        start += 1;
    }

    ans
}
