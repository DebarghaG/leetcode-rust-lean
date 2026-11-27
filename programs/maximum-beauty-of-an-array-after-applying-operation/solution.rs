pub fn maximum_beauty(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    let mut b: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        b.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;
        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + width + width < n {
                start + width + width
            } else {
                n
            };

            let mut left = start;
            let mut right = mid;
            let mut out = start;

            while left < mid && right < end {
                if a[left] <= a[right] {
                    b[out] = a[left];
                    left += 1;
                } else {
                    b[out] = a[right];
                    right += 1;
                }
                out += 1;
            }

            while left < mid {
                b[out] = a[left];
                left += 1;
                out += 1;
            }

            while right < end {
                b[out] = a[right];
                right += 1;
                out += 1;
            }

            start = end;
        }

        i = 0;
        while i < n {
            a[i] = b[i];
            i += 1;
        }

        width = width + width;
    }

    let limit = k + k;
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut best: i64 = 0;

    while right < n {
        while left <= right && a[right] - a[left] > limit {
            left += 1;
        }

        let current = (right - left + 1) as i64;
        if current > best {
            best = current;
        }

        right += 1;
    }

    best
}
