pub fn maximum_sum_of_heights(maxHeights: &[i64]) -> i64 {
    let n = maxHeights.len();
    if n == 0 {
        return 0;
    }

    let mut left: Vec<i64> = Vec::new();
    let mut right: Vec<i64> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();

    let mut init: usize = 0;
    while init < n {
        left.push(0);
        right.push(0);
        stack.push(0);
        init += 1;
    }

    let mut stack_len: usize = 0;
    let mut i: usize = 0;
    while i < n {
        let h = maxHeights[i];

        while stack_len > 0 {
            let top_idx = stack[stack_len - 1];
            if maxHeights[top_idx] > h {
                stack_len -= 1;
            } else {
                break;
            }
        }

        if stack_len == 0 {
            left[i] = h * ((i + 1) as i64);
        } else {
            let j = stack[stack_len - 1];
            let dist = (i - j) as i64;
            left[i] = left[j] + h * dist;
        }

        stack[stack_len] = i;
        stack_len += 1;
        i += 1;
    }

    stack_len = 0;
    let mut k: usize = n;
    while k > 0 {
        k -= 1;
        let h = maxHeights[k];

        while stack_len > 0 {
            let top_idx = stack[stack_len - 1];
            if maxHeights[top_idx] > h {
                stack_len -= 1;
            } else {
                break;
            }
        }

        if stack_len == 0 {
            let count = (n - k) as i64;
            right[k] = h * count;
        } else {
            let j = stack[stack_len - 1];
            let dist = (j - k) as i64;
            right[k] = right[j] + h * dist;
        }

        stack[stack_len] = k;
        stack_len += 1;
    }

    let mut ans: i64 = 0;
    let mut idx: usize = 0;
    while idx < n {
        let total = left[idx] + right[idx] - maxHeights[idx];
        if total > ans {
            ans = total;
        }
        idx += 1;
    }

    ans
}
