fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

pub fn subarray_lcm(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut l: i64 = 1;
        let mut j: usize = i;

        while j < n {
            let x = nums[j];
            let g = gcd(l, x);
            l = (l / g) * x;

            if l > k {
                break;
            }
            if k % l != 0 {
                break;
            }
            if l == k {
                ans += 1;
            }

            j += 1;
        }

        i += 1;
    }

    ans
}
