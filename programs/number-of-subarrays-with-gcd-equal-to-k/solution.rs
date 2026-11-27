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

pub fn subarray_gcd(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;

    let mut i = 0;
    while i < n {
        let mut g: i64 = 0;
        let mut j = i;
        while j < n {
            g = gcd(g, nums[j]);
            if g == k {
                ans += 1;
            }
            j += 1;
        }
        i += 1;
    }

    ans
}
