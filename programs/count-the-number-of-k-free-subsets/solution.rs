pub fn count_the_num_of_k_free_subsets(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    // Manual insertion sort.
    let mut i2 = 1;
    while i2 < n {
        let key = a[i2];
        let mut j = i2;
        while j > 0 {
            if a[j - 1] <= key {
                break;
            }
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = key;
        i2 += 1;
    }

    let mut ans: i64 = 1;

    let mut i = 0;
    while i < n {
        let rem = a[i] % k;

        let mut seen = false;
        let mut j = 0;
        while j < i {
            if a[j] % k == rem {
                seen = true;
                break;
            }
            j += 1;
        }

        if !seen {
            let mut dp0: i64 = 0;
            let mut dp1: i64 = 0;
            let mut prev: i64 = 0;
            let mut first = true;

            let mut t = 0;
            while t < n {
                if a[t] % k == rem {
                    if first {
                        dp0 = 1;
                        dp1 = 1;
                        first = false;
                    } else {
                        let new0 = dp0 + dp1;
                        let mut new1 = dp0 + dp1;

                        if a[t] - prev == k {
                            new1 = dp0;
                        }

                        dp0 = new0;
                        dp1 = new1;
                    }
                    prev = a[t];
                }
                t += 1;
            }

            let group_ways = dp0 + dp1;
            ans = ans * group_ways;
        }

        i += 1;
    }

    ans
}
