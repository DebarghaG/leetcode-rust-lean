fn is_prime(n: i64) -> bool {
    if n < 2 {
        return false;
    }
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }

    let mut d: i64 = 3;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 2;
    }

    true
}

pub fn maximum_prime_difference(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut first: i64 = -1;
    let mut last: i64 = -1;

    let mut i: usize = 0;
    while i < n {
        if is_prime(nums[i]) {
            if first == -1 {
                first = i as i64;
            }
            last = i as i64;
        }
        i += 1;
    }

    last - first
}
