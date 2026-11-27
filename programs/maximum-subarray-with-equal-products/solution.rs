fn gcd(a: i64, b: i64) -> i64 {
    let mut x = a;
    let mut y = b;
    while y != 0 {
        let r = x % y;
        x = y;
        y = r;
    }
    x
}

pub fn max_length(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n == 0 {
        return 0;
    }

    if n == 1 {
        if nums[0] == 1 {
            return 1;
        }
        return 0;
    }

    // Any subarray of length 2 is product equivalent.
    let mut best: i64 = 2;

    let mut start: usize = 0;
    while start < n {
        let mut end: usize = start;
        let mut cur_len: i64 = 0;
        let mut ok: bool = true;

        // For lengths >= 3, a subarray is product equivalent exactly when
        // all its elements are pairwise coprime.
        while end < n && ok {
            cur_len = cur_len + 1;

            let mut i: usize = start;
            while i < end {
                if gcd(nums[i], nums[end]) != 1 {
                    ok = false;
                }
                i += 1;
            }

            if ok {
                if cur_len > best {
                    best = cur_len;
                }
                end += 1;
            }
        }

        start += 1;
    }

    best
}
