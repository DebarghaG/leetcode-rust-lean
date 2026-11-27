pub fn valid_subarrays(nums: &[i64]) -> i64 {
    let n = nums.len() as i64;
    let mut ans: i64 = 0;
    let mut stack: Vec<i64> = Vec::new();

    let mut i: i64 = 0;
    while i < n {
        let cur = nums[i as usize];

        let mut can_pop = true;
        while can_pop {
            if stack.is_empty() {
                can_pop = false;
            } else {
                let top = stack[stack.len() - 1];
                if nums[top as usize] > cur {
                    ans = ans + (i - top);
                    stack.pop();
                } else {
                    can_pop = false;
                }
            }
        }

        stack.push(i);
        i = i + 1;
    }

    while !stack.is_empty() {
        let top = stack[stack.len() - 1];
        ans = ans + (n - top);
        stack.pop();
    }

    ans
}
