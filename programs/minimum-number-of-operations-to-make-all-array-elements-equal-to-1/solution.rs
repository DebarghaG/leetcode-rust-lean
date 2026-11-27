fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r: i64 = a % b;
        a = b;
        b = r;
    }
    a
}

pub fn min_operations(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let n_i: i64 = n as i64;

    let mut ones: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] == 1 {
            ones += 1;
        }
        i += 1;
    }

    if ones > 0 {
        return n_i - ones;
    }

    let mut best: i64 = n_i + 1;
    let mut start: usize = 0;

    while start < n {
        let mut g: i64 = nums[start];
        let mut end: usize = start;

        while end < n {
            if end > start {
                g = gcd(g, nums[end]);
            }

            if g == 1 {
                let len_i: i64 = (end - start + 1) as i64;
                if len_i < best {
                    best = len_i;
                }
                end = n;
            } else {
                end += 1;
            }
        }

        start += 1;
    }

    if best > n_i {
        return -1;
    }

    best + n_i - 2
}
