pub fn most_competitive(nums: &[i64], k: i64) -> Vec<i64> {
    let n: usize = nums.len();
    let kk: usize = k as usize;
    let mut stack: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        while stack.len() > 0
            && stack[stack.len() - 1] > nums[i]
            && stack.len() + (n - i) > kk
        {
            stack.pop();
        }

        if stack.len() < kk {
            stack.push(nums[i]);
        }

        i = i + 1;
    }

    stack
}
