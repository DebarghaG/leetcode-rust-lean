pub fn maximum_length(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut even: i64 = 0;
    let mut odd: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        if nums[i] % 2 == 0 {
            even += 1;
        } else {
            odd += 1;
        }
        i += 1;
    }

    let mut best = even;
    if odd > best {
        best = odd;
    }

    let mut alt: i64 = 1;
    let mut last: i64 = nums[0] % 2;

    i = 1;
    while i < n {
        let p = nums[i] % 2;
        if p != last {
            alt += 1;
            last = p;
        }
        i += 1;
    }

    if alt > best {
        best = alt;
    }

    best
}
