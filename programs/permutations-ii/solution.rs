pub fn permute_unique(nums: &[i64]) -> Vec<Vec<i64>> {
    let n = nums.len();
    let mut a: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    // Insertion sort the copied input in nondecreasing order.
    i = 1;
    while i < n {
        let key = a[i];
        let mut j = i;
        while j > 0 && a[j - 1] > key {
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = key;
        i += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    if n == 0 {
        return out;
    }

    loop {
        // Store the current permutation.
        let mut row: Vec<i64> = Vec::new();
        let mut t = 0;
        while t < n {
            row.push(a[t]);
            t += 1;
        }
        out.push(row);

        // Find the largest index p such that a[p] < a[p + 1].
        let mut p: usize = n;
        let mut idx = 0;
        while idx + 1 < n {
            if a[idx] < a[idx + 1] {
                p = idx;
            }
            idx += 1;
        }

        if p == n {
            break;
        }

        // Find the largest index q > p such that a[q] > a[p].
        let pivot = a[p];
        let mut cursor = n - 1;
        let mut q = p + 1;
        let mut found = false;

        while cursor > p {
            if a[cursor] > pivot {
                q = cursor;
                found = true;
                break;
            }
            cursor -= 1;
        }

        if !found {
            break;
        }

        // Swap a[p] and a[q].
        let tmp = a[p];
        a[p] = a[q];
        a[q] = tmp;

        // Reverse the suffix starting at p + 1.
        let mut left = p + 1;
        let mut right = n - 1;
        while left < right {
            let tmp2 = a[left];
            a[left] = a[right];
            a[right] = tmp2;

            left += 1;
            if right > 0 {
                right -= 1;
            } else {
                break;
            }
        }
    }

    out
}
