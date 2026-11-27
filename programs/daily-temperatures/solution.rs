pub fn daily_temperatures(temperatures: &[i64]) -> Vec<i64> {
    let n = temperatures.len();

    // Initialize the answer array with zeros.
    let mut ans: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        ans.push(0);
        i += 1;
    }

    // Monotonic decreasing stack of indices into `temperatures`.
    let mut stack: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        while stack.len() > 0 {
            let top = stack[stack.len() - 1];
            if temperatures[top] < temperatures[k] {
                ans[top] = (k - top) as i64;
                let _ = stack.pop();
            } else {
                break;
            }
        }
        stack.push(k);
        k += 1;
    }

    ans
}
