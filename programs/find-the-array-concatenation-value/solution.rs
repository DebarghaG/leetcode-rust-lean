pub fn find_the_array_conc_val(nums: &[i64]) -> i64 {
    let n = nums.len();
    let half = n / 2;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < half {
        let first = nums[i];
        let last = nums[n - 1 - i];

        let mut mult: i64 = 1;
        let mut temp = last;

        if temp == 0 {
            mult = 10;
        } else {
            while temp > 0 {
                mult = mult * 10;
                temp = temp / 10;
            }
        }

        ans = ans + first * mult + last;
        i = i + 1;
    }

    if n % 2 == 1 {
        ans = ans + nums[half];
    }

    ans
}
