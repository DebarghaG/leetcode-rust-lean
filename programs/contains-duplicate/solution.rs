pub fn contains_duplicate(nums: &[i64]) -> bool {
    let n = nums.len();
    if n <= 1 {
        return false;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut next: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }

            let mut end = start + width + width;
            if end > n {
                end = n;
            }

            let mut left = start;
            let mut right = mid;

            while left < mid && right < end {
                if v[left] <= v[right] {
                    next.push(v[left]);
                    left += 1;
                } else {
                    next.push(v[right]);
                    right += 1;
                }
            }

            while left < mid {
                next.push(v[left]);
                left += 1;
            }

            while right < end {
                next.push(v[right]);
                right += 1;
            }

            start = end;
        }

        v = next;
        width = width * 2;
    }

    let mut idx: usize = 1;
    while idx < n {
        if v[idx] == v[idx - 1] {
            return true;
        }
        idx += 1;
    }

    false
}
