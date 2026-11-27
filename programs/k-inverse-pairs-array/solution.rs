pub fn k_inverse_pairs(n: i64, k: i64) -> i64 {
    const MOD: i64 = 1000000007;

    if k < 0 {
        return 0;
    }
    if n <= 0 {
        if k == 0 {
            return 1;
        } else {
            return 0;
        }
    }
    if k > n * (n - 1) / 2 {
        return 0;
    }

    let n_us = n as usize;
    let k_us = k as usize;

    let mut prev: Vec<i64> = Vec::new();
    let mut curr: Vec<i64> = Vec::new();

    let mut t: usize = 0;
    while t <= k_us {
        prev.push(0);
        curr.push(0);
        t += 1;
    }
    prev[0] = 1;

    let mut i: usize = 1;
    while i <= n_us {
        let mut window: i64 = 0;
        let mut j: usize = 0;

        while j <= k_us {
            window += prev[j];
            if window >= MOD {
                window -= MOD;
            }

            if j >= i {
                window -= prev[j - i];
                if window < 0 {
                    window += MOD;
                }
            }

            curr[j] = window;
            j += 1;
        }

        let temp = prev;
        prev = curr;
        curr = temp;

        i += 1;
    }

    prev[k_us]
}
