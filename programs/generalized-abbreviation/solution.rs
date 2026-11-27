fn append_number(out: &mut Vec<u8>, count: usize) {
    let mut digits: Vec<u8> = Vec::new();
    let mut n = count;

    if n == 0 {
        digits.push(b'0');
    } else {
        while n > 0 {
            let d = (n % 10) as u8;
            digits.push(b'0' + d);
            n = n / 10;
        }
    }

    let mut i = digits.len();
    while i > 0 {
        i = i - 1;
        out.push(digits[i]);
    }
}

fn gen_from(word: &[u8], pos: usize, count: usize) -> Vec<Vec<u8>> {
    let n = word.len();
    let mut result: Vec<Vec<u8>> = Vec::new();

    if pos == n {
        let mut s: Vec<u8> = Vec::new();
        if count > 0 {
            append_number(&mut s, count);
        }
        result.push(s);
        return result;
    }

    // Option 1: keep word[pos] as a letter.
    let keep_suffixes = gen_from(word, pos + 1, 0);
    let mut i = 0;
    while i < keep_suffixes.len() {
        let mut out: Vec<u8> = Vec::new();

        if count > 0 {
            append_number(&mut out, count);
        }
        out.push(word[pos]);

        let suffix = &keep_suffixes[i];
        let mut j = 0;
        while j < suffix.len() {
            out.push(suffix[j]);
            j += 1;
        }

        result.push(out);
        i += 1;
    }

    // Option 2: abbreviate word[pos] together with any pending run.
    let abbrev_suffixes = gen_from(word, pos + 1, count + 1);
    let mut i2 = 0;
    while i2 < abbrev_suffixes.len() {
        let mut out: Vec<u8> = Vec::new();

        let suffix = &abbrev_suffixes[i2];
        let mut j = 0;
        while j < suffix.len() {
            out.push(suffix[j]);
            j += 1;
        }

        result.push(out);
        i2 += 1;
    }

    result
}

pub fn generate_abbreviations(word: &[u8]) -> Vec<Vec<u8>> {
    gen_from(word, 0, 0)
}
