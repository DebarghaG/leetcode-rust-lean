pub fn is_good(nums: &[i64]) -> bool {
    let len = nums.len();

    // Find the maximum value.
    let mut n: i64 = 0;
    let mut i: usize = 0;
    while i < len {
        if nums[i] > n {
            n = nums[i];
        }
        i += 1;
    }

    // Validate basic shape using flags (no early returns inside loops).
    let mut ok: bool = true;
    if len == 0 {
        ok = false;
    }
    if n < 1 {
        ok = false;
    }
    if (len as i64) != n + 1 {
        ok = false;
    }

    if ok {
        let mut counts: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j <= n as usize {
            counts.push(0);
            j += 1;
        }

        i = 0;
        while i < len {
            let x = nums[i];
            if x < 1 || x > n {
                ok = false;
            } else {
                let idx = x as usize;
                counts[idx] = counts[idx] + 1;
            }
            i += 1;
        }

        let mut v: usize = 1;
        while v < n as usize {
            if counts[v] != 1 {
                ok = false;
            }
            v += 1;
        }

        if counts[n as usize] != 2 {
            ok = false;
        }
    }

    ok
}
