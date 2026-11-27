pub fn validate_stack_sequences(pushed: &[i64], popped: &[i64]) -> bool {
    let n = pushed.len();
    let mut stack: Vec<i64> = Vec::new();
    let mut popped_index: usize = 0;
    let mut i: usize = 0;

    while i < n {
        stack.push(pushed[i]);

        while stack.len() > 0
            && popped_index < n
            && stack[stack.len() - 1] == popped[popped_index]
        {
            stack.pop();
            popped_index += 1;
        }

        i += 1;
    }

    popped_index == n && stack.len() == 0
}
