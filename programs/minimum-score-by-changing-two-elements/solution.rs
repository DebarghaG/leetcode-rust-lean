pub fn minimize_sum(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut mn0: i64 = 1000000000000000000;
    let mut mn1: i64 = 1000000000000000000;
    let mut mn2: i64 = 1000000000000000000;

    let mut mx0: i64 = -1000000000000000000;
    let mut mx1: i64 = -1000000000000000000;
    let mut mx2: i64 = -1000000000000000000;

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];

        if x < mn0 {
            mn2 = mn1;
            mn1 = mn0;
            mn0 = x;
        } else if x < mn1 {
            mn2 = mn1;
            mn1 = x;
        } else if x < mn2 {
            mn2 = x;
        }

        if x > mx2 {
            mx0 = mx1;
            mx1 = mx2;
            mx2 = x;
        } else if x > mx1 {
            mx0 = mx1;
            mx1 = x;
        } else if x > mx0 {
            mx0 = x;
        }

        i += 1;
    }

    let mut ans = mx2 - mn2;

    let d2 = mx1 - mn1;
    if d2 < ans {
        ans = d2;
    }

    let d3 = mx0 - mn0;
    if d3 < ans {
        ans = d3;
    }

    ans
}
