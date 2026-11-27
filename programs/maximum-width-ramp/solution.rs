pub fn max_width_ramp(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n <= 1 {
        return 0;
    }

    let mut stack: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let mut add = false;
        if stack.len() == 0 {
            add = true;
        } else {
            let top_idx = stack[stack.len() - 1];
            if nums[i] < nums[top_idx] {
                add = true;
            }
        }
        if add {
            stack.push(i);
        }
        i += 1;
    }

    let mut best: i64 = 0;
    let mut top: usize = stack.len();
    let mut j: usize = n;

    while j > 0 {
        j -= 1;
        let mut stop = false;
        while top > 0 && !stop {
            let idx = stack[top - 1];
            if nums[idx] <= nums[j] {
                if j >= idx {
                    let width = (j - idx) as i64;
                    if width > best {
                        best = width;
                    }
                }
                top -= 1;
            } else {
                stop = true;
            }
        }
    }

    best
}
