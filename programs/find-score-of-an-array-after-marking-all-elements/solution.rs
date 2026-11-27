pub fn find_score(nums: &[i64]) -> i64 {
    let n = nums.len();
    let base = n as i64;

    let mut keys: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let key = nums[i] * base + (i as i64);
        keys.push(key);
        i += 1;
    }

    // Bottom-up merge sort of encoded (value, index) keys.
    let mut width = 1usize;
    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut left = 0usize;
        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right = if left + width * 2 < n {
                left + width * 2
            } else {
                n
            };

            let mut p = left;
            let mut q = mid;
            while p < mid && q < right {
                if keys[p] <= keys[q] {
                    merged.push(keys[p]);
                    p += 1;
                } else {
                    merged.push(keys[q]);
                    q += 1;
                }
            }
            while p < mid {
                merged.push(keys[p]);
                p += 1;
            }
            while q < right {
                merged.push(keys[q]);
                q += 1;
            }

            left = right;
        }

        let mut t = 0usize;
        while t < n {
            keys[t] = merged[t];
            t += 1;
        }

        width = width * 2;
    }

    let mut marked: Vec<bool> = Vec::new();
    let mut j = 0usize;
    while j < n {
        marked.push(false);
        j += 1;
    }

    let mut score = 0i64;
    let mut k = 0usize;
    while k < n {
        let idx_i64 = keys[k] % base;
        let idx = idx_i64 as usize;

        if !marked[idx] {
            score += nums[idx];
            marked[idx] = true;

            if idx > 0 {
                marked[idx - 1] = true;
            }
            if idx + 1 < n {
                marked[idx + 1] = true;
            }
        }

        k += 1;
    }

    score
}
