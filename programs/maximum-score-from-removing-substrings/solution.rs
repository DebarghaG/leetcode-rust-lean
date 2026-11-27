pub fn maximum_gain(s: &[u8], x: i64, y: i64) -> i64 {
    let n = s.len();
    let mut score: i64 = 0;
    let mut stack: Vec<u8> = Vec::new();

    if x >= y {
        let mut i: usize = 0;
        while i < n {
            let c: u8 = s[i];
            if c == b'b' && stack.len() > 0 && stack[stack.len() - 1] == b'a' {
                stack.pop();
                score = score + x;
            } else {
                stack.push(c);
            }
            i += 1;
        }

        let mut second: Vec<u8> = Vec::new();
        let m = stack.len();
        let mut j: usize = 0;
        while j < m {
            let c: u8 = stack[j];
            if c == b'a' && second.len() > 0 && second[second.len() - 1] == b'b' {
                second.pop();
                score = score + y;
            } else {
                second.push(c);
            }
            j += 1;
        }
    } else {
        let mut i: usize = 0;
        while i < n {
            let c: u8 = s[i];
            if c == b'a' && stack.len() > 0 && stack[stack.len() - 1] == b'b' {
                stack.pop();
                score = score + y;
            } else {
                stack.push(c);
            }
            i += 1;
        }

        let mut second: Vec<u8> = Vec::new();
        let m = stack.len();
        let mut j: usize = 0;
        while j < m {
            let c: u8 = stack[j];
            if c == b'b' && second.len() > 0 && second[second.len() - 1] == b'a' {
                second.pop();
                score = score + x;
            } else {
                second.push(c);
            }
            j += 1;
        }
    }

    score
}
