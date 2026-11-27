pub fn max_operations(nums: &[i64], k: i64) -> i64 {
    let sorted = merge_sort(nums);
    let n = sorted.len();

    let mut left: usize = 0;
    let mut right: usize = n;
    let mut count: i64 = 0;

    while left + 1 < right {
        let sum = sorted[left] + sorted[right - 1];
        if sum == k {
            count += 1;
            left += 1;
            right -= 1;
        } else if sum < k {
            left += 1;
        } else {
            right -= 1;
        }
    }

    count
}

fn merge_sort(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    if n <= 1 {
        return a;
    }

    let mut width: usize = 1;
    while width < n {
        let step = width + width;
        let mut b: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }

            let mut end = start + step;
            if end > n {
                end = n;
            }

            let mut p = start;
            let mut q = mid;

            while p < mid && q < end {
                if a[p] <= a[q] {
                    b.push(a[p]);
                    p += 1;
                } else {
                    b.push(a[q]);
                    q += 1;
                }
            }

            while p < mid {
                b.push(a[p]);
                p += 1;
            }

            while q < end {
                b.push(a[q]);
                q += 1;
            }

            start += step;
        }

        a = b;
        width = step;
    }

    a
}
