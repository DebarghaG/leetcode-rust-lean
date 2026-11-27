pub fn find_maximums(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    if n == 0 {
        return Vec::new();
    }

    // left[i] = index of the previous element strictly smaller than nums[i], or -1.
    let mut left: Vec<i64> = Vec::new();
    let mut stack: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        while stack.len() > 0 {
            let top = stack[stack.len() - 1];
            let top_idx = top as usize;
            if nums[top_idx] < nums[i] {
                break;
            }
            stack.pop();
        }

        if stack.len() > 0 {
            left.push(stack[stack.len() - 1]);
        } else {
            left.push(-1);
        }

        stack.push(i as i64);
        i += 1;
    }

    // right[i] = index of the next element smaller than or equal to nums[i], or n.
    let mut right: Vec<i64> = Vec::new();
    let mut init: usize = 0;
    while init < n {
        right.push(n as i64);
        init += 1;
    }

    let mut stack2: Vec<i64> = Vec::new();
    let mut k: usize = n;
    while k > 0 {
        k -= 1;

        while stack2.len() > 0 {
            let top = stack2[stack2.len() - 1];
            let top_idx = top as usize;
            if nums[top_idx] > nums[k] {
                stack2.pop();
            } else {
                break;
            }
        }

        if stack2.len() > 0 {
            right[k] = stack2[stack2.len() - 1];
        } else {
            right[k] = n as i64;
        }

        stack2.push(k as i64);
    }

    // best[len - 1] stores the best minimum value for subarrays of size len.
    let mut best: Vec<i64> = Vec::new();
    let mut b: usize = 0;
    while b < n {
        best.push(-1);
        b += 1;
    }

    let mut idx: usize = 0;
    while idx < n {
        let len = right[idx] - left[idx] - 1;
        let len_idx = (len - 1) as usize;

        if nums[idx] > best[len_idx] {
            best[len_idx] = nums[idx];
        }

        idx += 1;
    }

    // If a value is achievable for size len, it is also achievable for every smaller size.
    let mut p: usize = n - 1;
    while p > 0 {
        let q = p - 1;
        if best[q] < best[p] {
            best[q] = best[p];
        }
        p -= 1;
    }

    best
}
