fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

pub fn min_operations(nums: &[i64], numsDivide: &[i64]) -> i64 {
    let n = nums.len();
    let m = numsDivide.len();

    let mut g = numsDivide[0];
    let mut i: usize = 1;
    while i < m {
        g = gcd(g, numsDivide[i]);
        i += 1;
    }

    let mut best: i64 = -1;
    i = 0;
    while i < n {
        let x = nums[i];
        if g % x == 0 {
            if best == -1 || x < best {
                best = x;
            }
        }
        i += 1;
    }

    if best == -1 {
        return -1;
    }

    let mut deletions: i64 = 0;
    i = 0;
    while i < n {
        if nums[i] < best {
            deletions += 1;
        }
        i += 1;
    }

    deletions
}
