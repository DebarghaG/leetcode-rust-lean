fn is_prime(n: i64) -> bool {
    if n < 2 {
        return false;
    }

    let mut d: i64 = 2;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }

    true
}

pub fn prime_sub_operation(nums: &[i64]) -> bool {
    let n = nums.len();
    let mut prev: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let cur = nums[i];
        let limit = cur - prev;

        // Default to not subtracting anything from cur.
        let mut chosen = cur;

        // We want the largest prime p such that p < limit,
        // because this makes cur - p as small as possible while still > prev.
        let mut p = limit - 1;
        while p >= 2 {
            if is_prime(p) {
                chosen = cur - p;
                p = 1;
            } else {
                p -= 1;
            }
        }

        if chosen <= prev {
            return false;
        }

        prev = chosen;
        i += 1;
    }

    true
}
