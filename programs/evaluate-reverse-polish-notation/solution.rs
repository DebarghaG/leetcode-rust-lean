pub fn eval_rpn(tokens: &[Vec<u8>]) -> i64 {
    let n = tokens.len();

    let mut stack: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        stack.push(0);
        k += 1;
    }

    let mut sp: usize = 0;
    let mut i: usize = 0;

    while i < n {
        let tok = &tokens[i];

        let mut is_op = false;
        if tok.len() == 1 {
            let c = tok[0];
            if c == b'+' || c == b'-' || c == b'*' || c == b'/' {
                is_op = true;
            }
        }

        if is_op {
            let rhs = stack[sp - 1];
            let lhs = stack[sp - 2];
            let c = tok[0];
            let mut res: i64 = 0;

            if c == b'+' {
                res = lhs + rhs;
            } else if c == b'-' {
                res = lhs - rhs;
            } else if c == b'*' {
                res = lhs * rhs;
            } else {
                res = lhs / rhs;
            }

            stack[sp - 2] = res;
            sp -= 1;
        } else {
            let mut pos: usize = 0;
            let mut neg = false;

            if tok.len() > 0 {
                if tok[0] == b'-' {
                    neg = true;
                    pos = 1;
                }
            }

            let mut val: i64 = 0;
            while pos < tok.len() {
                let digit = (tok[pos] - b'0') as i64;
                val = val * 10 + digit;
                pos += 1;
            }

            if neg {
                val = -val;
            }

            stack[sp] = val;
            sp += 1;
        }

        i += 1;
    }

    stack[0]
}
