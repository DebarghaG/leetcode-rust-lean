fn is_prime(x: i64) -> bool {
    if x < 2 {
        return false;
    }
    if x == 2 {
        return true;
    }
    if x % 2 == 0 {
        return false;
    }

    let mut d: i64 = 3;
    while d * d <= x {
        if x % d == 0 {
            return false;
        }
        d += 2;
    }
    true
}

pub fn diagonal_prime(nums: &[Vec<i64>]) -> i64 {
    let n: usize = nums.len();
    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let a: i64 = nums[i][i];
        if is_prime(a) && a > best {
            best = a;
        }

        let b: i64 = nums[i][n - i - 1];
        if is_prime(b) && b > best {
            best = b;
        }

        i += 1;
    }

    best
}
