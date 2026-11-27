fn max_i64(a: i64, b: i64) -> i64 {
    if a > b {
        a
    } else {
        b
    }
}

pub fn max_score(nums: &[i64], x: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let neg_inf: i64 = -1_000_000_000_000_000_000;

    let mut dp_even: i64 = neg_inf;
    let mut dp_odd: i64 = neg_inf;

    if nums[0] % 2 == 0 {
        dp_even = nums[0];
    } else {
        dp_odd = nums[0];
    }

    let mut i: usize = 1;
    while i < n {
        let v = nums[i];

        if v % 2 == 0 {
            let stay = dp_even;
            let switch = dp_odd - x;
            dp_even = max_i64(stay, switch) + v;
        } else {
            let stay = dp_odd;
            let switch = dp_even - x;
            dp_odd = max_i64(stay, switch) + v;
        }

        i = i + 1;
    }

    max_i64(dp_even, dp_odd)
}
