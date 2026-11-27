pub fn print_vertically(s: &[u8]) -> Vec<Vec<u8>> {
    let n: usize = s.len();

    // First pass: find the maximum word length.
    let mut max_len: usize = 0;
    let mut i: usize = 0;
    while i < n {
        while i < n && s[i] == b' ' {
            i += 1;
        }
        if i < n {
            let start: usize = i;
            while i < n && s[i] != b' ' {
                i += 1;
            }
            let len: usize = i - start;
            if len > max_len {
                max_len = len;
            }
        }
    }

    // Build one output row per character position.
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut r: usize = 0;
    while r < max_len {
        let mut row: Vec<u8> = Vec::new();
        let mut keep_len: usize = 0;

        i = 0;
        while i < n {
            while i < n && s[i] == b' ' {
                i += 1;
            }

            if i < n {
                let start: usize = i;
                while i < n && s[i] != b' ' {
                    i += 1;
                }

                let wlen: usize = i - start;
                let ch: u8 = if r < wlen { s[start + r] } else { b' ' };
                let idx: usize = row.len();
                row.push(ch);

                if ch != b' ' {
                    keep_len = idx + 1;
                }
            }
        }

        // Trim trailing spaces without relying on iterator methods.
        let mut trimmed: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while j < keep_len {
            trimmed.push(row[j]);
            j += 1;
        }

        out.push(trimmed);
        r += 1;
    }

    out
}
