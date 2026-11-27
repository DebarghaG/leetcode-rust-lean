pub fn calculate(s: &[u8]) -> i64 {
    let mut stack: Vec<i64> = Vec::new();
    let mut num: i64 = 0;
    let mut op: u8 = b'+';
    let mut i: usize = 0;

    while i < s.len() {
        let c = s[i];

        if c >= b'0' && c <= b'9' {
            num = num * 10 + ((c - b'0') as i64);
        } else if c == b' ' || c == b'(' || c == b')' {
            // Skip spaces and parentheses.
        } else {
            if op == b'+' {
                stack.push(num);
            } else if op == b'-' {
                stack.push(-num);
            } else if op == b'*' {
                let n = stack.len();
                let last = stack[n - 1];
                stack[n - 1] = last * num;
            } else if op == b'/' {
                let n = stack.len();
                let last = stack[n - 1];
                stack[n - 1] = last / num;
            }

            op = c;
            num = 0;
        }

        i += 1;
    }

    if op == b'+' {
        stack.push(num);
    } else if op == b'-' {
        stack.push(-num);
    } else if op == b'*' {
        let n = stack.len();
        let last = stack[n - 1];
        stack[n - 1] = last * num;
    } else if op == b'/' {
        let n = stack.len();
        let last = stack[n - 1];
        stack[n - 1] = last / num;
    }

    let mut ans: i64 = 0;
    let mut j: usize = 0;
    while j < stack.len() {
        ans += stack[j];
        j += 1;
    }

    ans
}
