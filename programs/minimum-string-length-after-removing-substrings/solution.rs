pub fn min_length(s: &[u8]) -> i64 {
    let mut stack: Vec<u8> = Vec::new();
    let mut i: usize = 0;

    while i < s.len() {
        let c = s[i];
        let mut removed = false;

        if stack.len() > 0 {
            let top = stack[stack.len() - 1];
            if (top == b'A' && c == b'B') || (top == b'C' && c == b'D') {
                stack.pop();
                removed = true;
            }
        }

        if !removed {
            stack.push(c);
        }

        i += 1;
    }

    stack.len() as i64
}
