pub fn max_sum_after_operation(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let first = nums[0];

    // Maximum subarray sum ending at the current index without using the operation.
    let mut best_no_op = first;

    // Maximum subarray sum ending at the current index after using the operation exactly once.
    let mut best_used_op = first * first;

    let mut answer = best_used_op;

    let mut i: usize = 1;
    while i < n {
        let x = nums[i];
        let square = x * x;

        // Continue a subarray where the operation was already used earlier.
        let mut new_used = best_used_op + x;

        // Start using the operation at the current index, extending a no-operation prefix.
        let use_now = best_no_op + square;
        if use_now > new_used {
            new_used = use_now;
        }

        // Start a new subarray at the current index and use the operation here.
        if square > new_used {
            new_used = square;
        }

        // Update the no-operation state.
        let mut new_no_op = x;
        let extend_no_op = best_no_op + x;
        if extend_no_op > new_no_op {
            new_no_op = extend_no_op;
        }

        best_no_op = new_no_op;
        best_used_op = new_used;

        if best_used_op > answer {
            answer = best_used_op;
        }

        i += 1;
    }

    answer
}
