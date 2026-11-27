pub fn is_prefix_string(s: &[u8], words: &[Vec<u8>]) -> bool {
    let n: usize = s.len();
    let mut pos: usize = 0;
    let mut i: usize = 0;
    let mut result: bool = false;
    let mut finished: bool = false;

    while i < words.len() && !finished {
        let w = &words[i];
        let wlen: usize = w.len();
        let mut j: usize = 0;
        let mut mismatch: bool = false;

        while j < wlen && !mismatch {
            if pos >= n {
                mismatch = true;
            } else if s[pos] != w[j] {
                mismatch = true;
            } else {
                pos += 1;
                j += 1;
            }
        }

        if mismatch {
            finished = true;
        } else if pos == n {
            result = true;
            finished = true;
        } else {
            i += 1;
        }
    }

    result
}
