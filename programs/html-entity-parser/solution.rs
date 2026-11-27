fn slice_eq(text: &[u8], pos: usize, pat: &[u8], end: usize) -> bool {
    let plen = pat.len();
    if pos > end {
        return false;
    }
    if plen > end - pos {
        return false;
    }
    let mut j: usize = 0;
    while j < plen {
        if text[pos + j] != pat[j] {
            return false;
        }
        j = j + 1;
    }
    true
}

pub fn entity_parser(text: &[u8]) -> Vec<u8> {
    let n = text.len();
    let mut start: usize = 0;
    let mut end: usize = n;

    if n >= 12 {
        if slice_eq(text, 0, b"&quot;", n) {
            if slice_eq(text, n - 6, b"&quot;", n) {
                start = 6;
                end = n - 6;
            }
        }
    }

    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = start;

    while i < end {
        if text[i] == b'&' {
            if slice_eq(text, i, b"&quot;", end) {
                out.push(b'"');
                i = i + 6;
            } else if slice_eq(text, i, b"&apos;", end) {
                out.push(39u8);
                i = i + 6;
            } else if slice_eq(text, i, b"&amp;", end) {
                out.push(b'&');
                i = i + 5;
            } else if slice_eq(text, i, b"&gt;", end) {
                out.push(b'>');
                i = i + 4;
            } else if slice_eq(text, i, b"&lt;", end) {
                out.push(b'<');
                i = i + 4;
            } else if slice_eq(text, i, b"&frasl;", end) {
                out.push(47u8);
                i = i + 7;
            } else {
                out.push(text[i]);
                i = i + 1;
            }
        } else {
            out.push(text[i]);
            i = i + 1;
        }
    }

    out
}
