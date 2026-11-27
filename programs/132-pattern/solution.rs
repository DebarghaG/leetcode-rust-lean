pub fn find132pattern(nums: &[i64]) -> bool {
    let n = nums.len();
    let mut stack: Vec<i64> = Vec::new();
    let mut third: i64 = 0;
    let mut has_third: bool = false;

    let mut i = n;
    while i > 0 {
        i -= 1;
        let x = nums[i];

        while stack.len() > 0 && stack[stack.len() - 1] < x {
            third = stack[stack.len() - 1];
            has_third = true;
            stack.pop();
        }

        if has_third && x < third {
            return true;
        }

        stack.push(x);
    }

    false
}
