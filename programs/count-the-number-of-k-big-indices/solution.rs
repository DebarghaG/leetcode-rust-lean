pub fn k_big_indices(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let n_i = n as i64;

    let mut left_ok: Vec<bool> = Vec::new();
    let mut t = 0;
    while t < n {
        left_ok.push(false);
        t += 1;
    }

    // lowbit[i] = largest power of two dividing i, for 1 <= i <= n.
    let mut lowbit: Vec<i64> = Vec::new();
    let mut t2 = 0;
    while t2 <= n {
        lowbit.push(0);
        t2 += 1;
    }

    let mut i = 1;
    while i <= n {
        if i == 1 {
            lowbit[1] = 1;
        } else if i % 2 == 0 {
            lowbit[i] = lowbit[i / 2] * 2;
        } else {
            lowbit[i] = 1;
        }
        i += 1;
    }

    // Fenwick tree over values 1..=n.
    let mut bit: Vec<i64> = Vec::new();
    let mut t3 = 0;
    while t3 <= n {
        bit.push(0);
        t3 += 1;
    }

    // First pass: count smaller values strictly to the left.
    let mut i = 0;
    while i < n {
        let v = nums[i];

        let mut q = v - 1;
        let mut cnt: i64 = 0;
        while q > 0 {
            cnt += bit[q as usize];
            q -= lowbit[q as usize];
        }

        if cnt >= k {
            left_ok[i] = true;
        }

        let mut p = v;
        while p <= n_i {
            bit[p as usize] += 1;
            p += lowbit[p as usize];
        }

        i += 1;
    }

    // Clear the Fenwick tree.
    let mut t4 = 0;
    while t4 <= n {
        bit[t4] = 0;
        t4 += 1;
    }

    // Second pass: count smaller values strictly to the right.
    let mut ans: i64 = 0;
    let mut i2 = n;
    while i2 > 0 {
        i2 -= 1;
        let v = nums[i2];

        let mut q = v - 1;
        let mut cnt: i64 = 0;
        while q > 0 {
            cnt += bit[q as usize];
            q -= lowbit[q as usize];
        }

        if left_ok[i2] && cnt >= k {
            ans += 1;
        }

        let mut p = v;
        while p <= n_i {
            bit[p as usize] += 1;
            p += lowbit[p as usize];
        }
    }

    ans
}
