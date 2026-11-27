pub fn max_sum_min_product(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);
    let mut i: usize = 0;
    while i < n {
        let next_sum = prefix[i] + nums[i];
        prefix.push(next_sum);
        i += 1;
    }

    let mut stack: Vec<usize> = Vec::new();
    let mut best: i64 = 0;

    i = 0;
    while i < n {
        while stack.len() > 0 {
            let top: usize = stack[stack.len() - 1];
            if nums[top] >= nums[i] {
                stack.pop();

                let left: usize = if stack.len() > 0 {
                    stack[stack.len() - 1] + 1
                } else {
                    0
                };

                let subarray_sum: i64 = prefix[i] - prefix[left];
                let product: i64 = nums[top] * subarray_sum;
                if product > best {
                    best = product;
                }
            } else {
                break;
            }
        }

        stack.push(i);
        i += 1;
    }

    while stack.len() > 0 {
        let top: usize = stack[stack.len() - 1];
        stack.pop();

        let left: usize = if stack.len() > 0 {
            stack[stack.len() - 1] + 1
        } else {
            0
        };

        let subarray_sum: i64 = prefix[n] - prefix[left];
        let product: i64 = nums[top] * subarray_sum;
        if product > best {
            best = product;
        }
    }

    best % 1000000007
}
