pub fn min_increment_for_unique(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    let mut vals: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        vals.push(nums[i]);
        i = i + 1;
    }

    let mut temp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        temp.push(0);
        i = i + 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = left + width + width;
            if right > n {
                right = n;
            }

            let mut a: usize = left;
            let mut b: usize = mid;
            let mut k: usize = left;

            while a < mid && b < right {
                if vals[a] <= vals[b] {
                    temp[k] = vals[a];
                    a = a + 1;
                } else {
                    temp[k] = vals[b];
                    b = b + 1;
                }
                k = k + 1;
            }

            while a < mid {
                temp[k] = vals[a];
                a = a + 1;
                k = k + 1;
            }

            while b < right {
                temp[k] = vals[b];
                b = b + 1;
                k = k + 1;
            }

            left = left + width + width;
        }

        i = 0;
        while i < n {
            vals[i] = temp[i];
            i = i + 1;
        }

        width = width + width;
    }

    let mut ans: i64 = 0;
    let mut previous: i64 = -1;

    i = 0;
    while i < n {
        let value: i64 = vals[i];
        if value > previous {
            previous = value;
        } else {
            previous = previous + 1;
            ans = ans + (previous - value);
        }
        i = i + 1;
    }

    ans
}
