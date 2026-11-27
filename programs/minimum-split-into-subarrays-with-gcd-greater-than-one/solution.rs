fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

pub fn minimum_splits(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut splits: i64 = 1;
    let mut current_gcd: i64 = nums[0];

    let mut i: usize = 1;
    while i < n {
        current_gcd = gcd(current_gcd, nums[i]);
        if current_gcd == 1 {
            splits += 1;
            current_gcd = nums[i];
        }
        i += 1;
    }

    splits
}
