pub fn min_difference(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n <= 4 {
        return 0;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    v.sort();

    let d0 = v[n - 1] - v[3];
    let d1 = v[n - 2] - v[2];
    let d2 = v[n - 3] - v[1];
    let d3 = v[n - 4] - v[0];

    let mut ans = d0;
    if d1 < ans {
        ans = d1;
    }
    if d2 < ans {
        ans = d2;
    }
    if d3 < ans {
        ans = d3;
    }

    ans
}
