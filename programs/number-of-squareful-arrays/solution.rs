pub fn num_squareful_perms(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    let total_masks: usize = 1usize << n;
    let dp_size: usize = total_masks * n;

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < dp_size {
        dp.push(0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let mask: usize = 1usize << i;
        dp[mask * n + i] = 1;
        i += 1;
    }

    let mut compat: Vec<bool> = Vec::new();
    let compat_size: usize = n * n;
    let mut c: usize = 0;
    while c < compat_size {
        compat.push(false);
        c += 1;
    }

    let mut a: usize = 0;
    while a < n {
        let mut b: usize = 0;
        while b < n {
            if is_square(nums[a] + nums[b]) {
                compat[a * n + b] = true;
            }
            b += 1;
        }
        a += 1;
    }

    let mut mask: usize = 1;
    while mask < total_masks {
        let mut last: usize = 0;
        while last < n {
            let last_bit: usize = 1usize << last;
            if (mask & last_bit) != 0 {
                let val: i64 = dp[mask * n + last];
                if val != 0 {
                    let mut next: usize = 0;
                    while next < n {
                        let next_bit: usize = 1usize << next;
                        if (mask & next_bit) == 0 {
                            if compat[last * n + next] {
                                let new_mask: usize = mask | next_bit;
                                let idx: usize = new_mask * n + next;
                                dp[idx] = dp[idx] + val;
                            }
                        }
                        next += 1;
                    }
                }
            }
            last += 1;
        }
        mask += 1;
    }

    let full: usize = total_masks - 1;
    let mut total: i64 = 0;
    let mut last_idx: usize = 0;
    while last_idx < n {
        total += dp[full * n + last_idx];
        last_idx += 1;
    }

    let mut counted: Vec<bool> = Vec::new();
    let mut q: usize = 0;
    while q < n {
        counted.push(false);
        q += 1;
    }

    let mut divisor: i64 = 1;
    let mut x: usize = 0;
    while x < n {
        if !counted[x] {
            let mut count: i64 = 0;
            let mut y: usize = 0;
            while y < n {
                if nums[x] == nums[y] {
                    count += 1;
                    counted[y] = true;
                }
                y += 1;
            }
            divisor = divisor * factorial(count);
        }
        x += 1;
    }

    total / divisor
}

fn is_square(x: i64) -> bool {
    let mut r: i64 = 0;
    while r * r <= x {
        if r * r == x {
            return true;
        }
        r += 1;
    }
    false
}

fn factorial(n: i64) -> i64 {
    let mut result: i64 = 1;
    let mut i: i64 = 2;
    while i <= n {
        result = result * i;
        i += 1;
    }
    result
}
