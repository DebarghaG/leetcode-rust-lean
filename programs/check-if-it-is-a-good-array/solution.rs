pub fn is_good_array(nums: &[i64]) -> bool {
    if nums.len() == 0 {
        return false;
    }

    let mut g: i64 = nums[0];

    let mut i: usize = 1;
    while i < nums.len() {
        g = gcd_i64(g, nums[i]);
        if g == 1 {
            return true;
        }
        i += 1;
    }

    g == 1
}

fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r: i64 = a % b;
        a = b;
        b = r;
    }
    a
}
