pub fn split_array(nums: &[i64]) -> bool {
    let n = nums.len();
    if n < 7 {
        return false;
    }

    // prefix[t] = sum of nums[0..t-1], length n+1
    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);
    let mut idx = 0usize;
    while idx < n {
        let next = prefix[idx] + nums[idx];
        prefix.push(next);
        idx += 1;
    }

    // Sort a copy of all prefix sums.
    let mut vals: Vec<i64> = Vec::new();
    idx = 0usize;
    while idx < prefix.len() {
        vals.push(prefix[idx]);
        idx += 1;
    }

    let m = vals.len();
    let mut a = 1usize;
    while a < m {
        let key = vals[a];
        let mut b = a;
        while b > 0 && vals[b - 1] > key {
            vals[b] = vals[b - 1];
            b -= 1;
        }
        vals[b] = key;
        a += 1;
    }

    // Build sorted unique values.
    let mut unique: Vec<i64> = Vec::new();
    idx = 0usize;
    while idx < vals.len() {
        if idx == 0 || vals[idx] != vals[idx - 1] {
            unique.push(vals[idx]);
        }
        idx += 1;
    }

    let ulen = unique.len();
    let mut found = false;

    // j is the second removed position.
    let mut j = 3usize;
    while j + 4 <= n && !found {
        let mut marked: Vec<bool> = Vec::new();
        let mut u = 0usize;
        while u < ulen {
            marked.push(false);
            u += 1;
        }

        // Mark sums of the first segment matchable by the second segment.
        let mut i = 1usize;
        while i + 1 < j {
            if prefix[i] + prefix[i + 1] == prefix[j] {
                let s = prefix[i];
                let mut lo = 0usize;
                let mut hi = ulen;
                while lo < hi {
                    let mid = (lo + hi) / 2;
                    if unique[mid] < s {
                        lo = mid + 1;
                    } else {
                        hi = mid;
                    }
                }
                if lo < ulen && unique[lo] == s {
                    marked[lo] = true;
                }
            }
            i += 1;
        }

        // Try all possible k positions.
        let mut k = j + 2;
        while k + 1 < n && !found {
            let third_sum = prefix[k] - prefix[j + 1];
            let fourth_sum = prefix[n] - prefix[k + 1];

            if third_sum == fourth_sum {
                let s = third_sum;
                let mut lo = 0usize;
                let mut hi = ulen;
                while lo < hi {
                    let mid = (lo + hi) / 2;
                    if unique[mid] < s {
                        lo = mid + 1;
                    } else {
                        hi = mid;
                    }
                }
                if lo < ulen && unique[lo] == s && marked[lo] {
                    found = true;
                }
            }

            k += 1;
        }

        j += 1;
    }

    found
}
