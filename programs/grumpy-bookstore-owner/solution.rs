pub fn max_satisfied(customers: &[i64], grumpy: &[i64], minutes: i64) -> i64 {
    let n = customers.len();
    if n == 0 {
        return 0;
    }

    let mut base: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if grumpy[i] == 0 {
            base += customers[i];
        }
        i += 1;
    }

    let mut k: usize = 0;
    if minutes > 0 {
        k = minutes as usize;
    }
    if k > n {
        k = n;
    }
    if k == 0 {
        return base;
    }

    let mut window_extra: i64 = 0;
    let mut j: usize = 0;
    while j < k {
        if grumpy[j] == 1 {
            window_extra += customers[j];
        }
        j += 1;
    }

    let mut best_extra: i64 = window_extra;
    let mut start: usize = 1;

    while start + k <= n {
        let out_idx = start - 1;
        if grumpy[out_idx] == 1 {
            window_extra -= customers[out_idx];
        }

        let in_idx = start + k - 1;
        if grumpy[in_idx] == 1 {
            window_extra += customers[in_idx];
        }

        if window_extra > best_extra {
            best_extra = window_extra;
        }

        start += 1;
    }

    base + best_extra
}
