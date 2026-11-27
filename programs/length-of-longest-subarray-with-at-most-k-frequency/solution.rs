pub fn max_subarray_length(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let sorted = sorted_copy(nums);

    let mut unique: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        if i == 0 {
            unique.push(sorted[i]);
        } else {
            if sorted[i] != sorted[i - 1] {
                unique.push(sorted[i]);
            }
        }
        i += 1;
    }

    let m = unique.len();
    let mut freq: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        freq.push(0);
        i += 1;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut best: i64 = 0;
    let mut window_len: i64 = 0;

    while right < n {
        let value = nums[right];
        let idx = lower_bound(&unique, value);
        freq[idx] = freq[idx] + 1;
        window_len = window_len + 1;

        while freq[idx] > k {
            let left_value = nums[left];
            let left_idx = lower_bound(&unique, left_value);
            freq[left_idx] = freq[left_idx] - 1;
            left += 1;
            window_len = window_len - 1;
        }

        if window_len > best {
            best = window_len;
        }

        right += 1;
    }

    best
}

fn lower_bound(xs: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

fn sorted_copy(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut v: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    if n <= 1 {
        return v;
    }

    let mut temp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        temp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;

        while start < n {
            let mid = if start + width < n {
                start + width
            } else {
                n
            };

            let end = if start + width + width < n {
                start + width + width
            } else {
                n
            };

            let mut a = start;
            let mut b = mid;
            let mut t = start;

            while a < mid && b < end {
                if v[a] <= v[b] {
                    temp[t] = v[a];
                    a += 1;
                } else {
                    temp[t] = v[b];
                    b += 1;
                }
                t += 1;
            }

            while a < mid {
                temp[t] = v[a];
                a += 1;
                t += 1;
            }

            while b < end {
                temp[t] = v[b];
                b += 1;
                t += 1;
            }

            start = end;
        }

        let mut j: usize = 0;
        while j < n {
            v[j] = temp[j];
            j += 1;
        }

        width = width + width;
    }

    v
}
