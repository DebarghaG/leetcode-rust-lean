pub fn is_valid(s: &[u8]) -> bool {
    let mut stack: Vec<u8> = Vec::new();
    let n = s.len();
    let mut i: usize = 0;

    while i < n {
        let c = s[i];

        if c == b'(' || c == b'[' || c == b'{' {
            stack.push(c);
        } else {
            if stack.len() == 0 {
                return false;
            }

            let top = stack[stack.len() - 1];

            if c == b')' {
                if top != b'(' {
                    return false;
                }
            } else if c == b']' {
                if top != b'[' {
                    return false;
                }
            } else if c == b'}' {
                if top != b'{' {
                    return false;
                }
            } else {
                return false;
            }

            stack.pop();
        }

        i = i + 1;
    }

    stack.len() == 0
}
