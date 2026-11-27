pub fn partition_array(nums: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    // Copy the input into an owned vector so it can be sorted in place.
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    // Auxiliary vector for iterative bottom-up merge sort.
    let mut temp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        temp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let double_width: usize = width * 2;
        let mut left: usize = 0;

        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = left + double_width;
            if right > n {
                right = n;
            }

            let mut p: usize = left;
            let mut q: usize = mid;
            let mut out: usize = left;

            while p < mid && q < right {
                if a[p] <= a[q] {
                    temp[out] = a[p];
                    p += 1;
                } else {
                    temp[out] = a[q];
                    q += 1;
                }
                out += 1;
            }

            while p < mid {
                temp[out] = a[p];
                p += 1;
                out += 1;
            }

            while q < right {
                temp[out] = a[q];
                q += 1;
                out += 1;
            }

            left = right;
        }

        i = 0;
        while i < n {
            a[i] = temp[i];
            i += 1;
        }

        width = double_width;
    }

    // Greedy scan over the sorted values.
    let mut groups: i64 = 1;
    let mut current_start: i64 = a[0];

    i = 1;
    while i < n {
        if a[i] - current_start > k {
            groups += 1;
            current_start = a[i];
        }
        i += 1;
    }

    groups
}
