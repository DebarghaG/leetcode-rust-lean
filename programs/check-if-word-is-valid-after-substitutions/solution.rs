pub fn is_valid(s: &[u8]) -> bool {
    let mut stack: Vec<u8> = Vec::new();
    let mut top: usize = 0;
    let mut i: usize = 0;

    while i < s.len() {
        let ch = s[i];

        if top < stack.len() {
            stack[top] = ch;
        } else {
            stack.push(ch);
        }
        top += 1;

        if top >= 3
            && stack[top - 3] == b'a'
            && stack[top - 2] == b'b'
            && stack[top - 1] == b'c'
        {
            top -= 3;
        }

        i += 1;
    }

    top == 0
}
