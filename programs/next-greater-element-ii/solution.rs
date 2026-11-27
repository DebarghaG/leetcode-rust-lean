pub fn next_greater_elements(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut ans: Vec<i64> = Vec::new();

    if n == 0 {
        return ans;
    }

    let mut i = 0;
    while i < n {
        ans.push(-1);
        i += 1;
    }

    let mut stack: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < 2 * n {
        let idx = k % n;

        while stack.len() > 0 {
            let top = stack[stack.len() - 1] as usize;
            if nums[top] < nums[idx] {
                stack.pop();
                ans[top] = nums[idx];
            } else {
                break;
            }
        }

        if k < n {
            stack.push(idx as i64);
        }

        k += 1;
    }

    ans
}
