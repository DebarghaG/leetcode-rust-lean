pub fn count_subarrays(nums: &[i64], minK: i64, maxK: i64) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;
    let mut left: usize = 0;
    let mut last_min: usize = n;
    let mut last_max: usize = n;
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];

        if x < minK || x > maxK {
            left = i + 1;
            last_min = n;
            last_max = n;
        } else {
            if x == minK {
                last_min = i;
            }
            if x == maxK {
                last_max = i;
            }

            if last_min < n && last_max < n {
                let m = if last_min < last_max {
                    last_min
                } else {
                    last_max
                };
                ans += (m - left + 1) as i64;
            }
        }

        i += 1;
    }

    ans
}
