pub fn sum_subarray_mins(arr: &[i64]) -> i64 {
    let n = arr.len();
    let modv: i64 = 1000000007;

    let mut left: Vec<i64> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        while stack.len() > 0 {
            let top = stack[stack.len() - 1];
            if arr[top] >= arr[i] {
                stack.pop();
            } else {
                break;
            }
        }

        let prev: i64 = if stack.len() == 0 {
            -1
        } else {
            let top = stack[stack.len() - 1];
            top as i64
        };

        left.push(i as i64 - prev);
        stack.push(i);
        i = i + 1;
    }

    let mut ans: i64 = 0;
    let mut stack2: Vec<usize> = Vec::new();

    let mut j: usize = n;
    while j > 0 {
        j = j - 1;
        let idx = j;

        while stack2.len() > 0 {
            let top = stack2[stack2.len() - 1];
            if arr[top] > arr[idx] {
                stack2.pop();
            } else {
                break;
            }
        }

        let next: i64 = if stack2.len() == 0 {
            n as i64
        } else {
            let top = stack2[stack2.len() - 1];
            top as i64
        };

        let right_count: i64 = next - idx as i64;
        let left_count: i64 = left[idx];
        let contribution: i64 = arr[idx] * left_count * right_count;

        ans = (ans + contribution % modv) % modv;
        stack2.push(idx);
    }

    ans
}
