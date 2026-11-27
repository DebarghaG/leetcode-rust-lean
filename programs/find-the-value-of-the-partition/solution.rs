pub fn find_value_of_partition(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }

            let mut end = mid + width;
            if end > n {
                end = n;
            }

            let mut left = start;
            let mut right = mid;

            while left < mid && right < end {
                if v[left] <= v[right] {
                    merged.push(v[left]);
                    left += 1;
                } else {
                    merged.push(v[right]);
                    right += 1;
                }
            }

            while left < mid {
                merged.push(v[left]);
                left += 1;
            }

            while right < end {
                merged.push(v[right]);
                right += 1;
            }

            start = end;
        }

        let mut k: usize = 0;
        while k < n {
            v[k] = merged[k];
            k += 1;
        }

        width = width * 2;
    }

    let mut ans = v[1] - v[0];
    let mut j: usize = 1;
    while j + 1 < n {
        let diff = v[j + 1] - v[j];
        if diff < ans {
            ans = diff;
        }
        j += 1;
    }

    ans
}
