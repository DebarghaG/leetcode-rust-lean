pub fn get_maximum_consecutive(coins: &[i64]) -> i64 {
    let n = coins.len();
    if n == 0 {
        return 1;
    }

    // Copy the input into an owned vector so it can be sorted.
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(coins[i]);
        i += 1;
    }

    // Temporary buffer for iterative bottom-up merge sort.
    let mut b: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        b.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;

        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = left + width * 2;
            if right > n {
                right = n;
            }

            let mut p: usize = left;
            let mut q: usize = mid;
            let mut k: usize = left;

            while p < mid && q < right {
                let x = a[p];
                let y = a[q];
                if x <= y {
                    b[k] = x;
                    p += 1;
                } else {
                    b[k] = y;
                    q += 1;
                }
                k += 1;
            }

            while p < mid {
                b[k] = a[p];
                p += 1;
                k += 1;
            }

            while q < right {
                b[k] = a[q];
                q += 1;
                k += 1;
            }

            left = right;
        }

        let mut t: usize = 0;
        while t < n {
            a[t] = b[t];
            t += 1;
        }

        width = width * 2;
    }

    // Greedily extend the interval [0, reachable) of constructible sums.
    let mut reachable: i64 = 1;
    let mut idx: usize = 0;

    while idx < n {
        let c = a[idx];
        if c <= reachable {
            reachable = reachable + c;
            idx += 1;
        } else {
            return reachable;
        }
    }

    reachable
}
