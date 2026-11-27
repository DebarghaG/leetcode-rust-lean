pub fn ways_to_make_fair(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut total_even: i64 = 0;
    let mut total_odd: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        if i % 2 == 0 {
            total_even += nums[i];
        } else {
            total_odd += nums[i];
        }
        i += 1;
    }

    let mut left_even: i64 = 0;
    let mut left_odd: i64 = 0;
    let mut ans: i64 = 0;

    i = 0;
    while i < n {
        let x = nums[i];

        let mut right_even = total_even - left_even;
        let mut right_odd = total_odd - left_odd;

        if i % 2 == 0 {
            right_even -= x;
        } else {
            right_odd -= x;
        }

        if left_even + right_odd == left_odd + right_even {
            ans += 1;
        }

        if i % 2 == 0 {
            left_even += x;
        } else {
            left_odd += x;
        }

        i += 1;
    }

    ans
}
