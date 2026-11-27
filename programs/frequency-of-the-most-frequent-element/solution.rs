fn merge_sort(mut v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if n < 2 {
        return v;
    }

    let mut width: usize = 1;
    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mid = if start + width < n {
                start + width
            } else {
                n
            };

            let two_width = start + width + width;
            let end = if two_width < n { two_width } else { n };

            let mut i: usize = start;
            let mut j: usize = mid;

            while i < mid && j < end {
                if v[i] <= v[j] {
                    merged.push(v[i]);
                    i += 1;
                } else {
                    merged.push(v[j]);
                    j += 1;
                }
            }

            while i < mid {
                merged.push(v[i]);
                i += 1;
            }

            while j < end {
                merged.push(v[j]);
                j += 1;
            }

            start = end;
        }

        v = merged;
        width = width + width;
    }

    v
}

pub fn max_frequency(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut copied: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        copied.push(nums[i]);
        i += 1;
    }

    let sorted = merge_sort(copied);

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut sum: i64 = 0;
    let mut best: i64 = 0;

    while right < n {
        sum = sum + sorted[right];

        while left <= right {
            let count = (right - left + 1) as i64;
            let target = sorted[right] * count;
            if target - sum <= k {
                break;
            }
            sum = sum - sorted[left];
            left += 1;
        }

        if left <= right {
            let count = (right - left + 1) as i64;
            if count > best {
                best = count;
            }
        }

        right += 1;
    }

    best
}
