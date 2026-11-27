pub fn string_sequence(target: &[u8]) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let n: usize = target.len();

    let mut i: usize = 0;
    while i < n {
        let goal: u8 = target[i];
        let mut c: u8 = b'a';
        let mut keep_going: bool = true;

        while keep_going {
            let mut s: Vec<u8> = Vec::new();
            let mut j: usize = 0;

            while j < i {
                s.push(target[j]);
                j += 1;
            }

            s.push(c);
            out.push(s);

            if c == goal {
                keep_going = false;
            } else {
                c = c + 1;
            }
        }

        i += 1;
    }

    out
}
