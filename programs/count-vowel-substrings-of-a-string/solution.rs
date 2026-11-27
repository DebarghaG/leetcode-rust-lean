fn is_vowel(c: u8) -> bool {
    c == b'a' || c == b'e' || c == b'i' || c == b'o' || c == b'u'
}

pub fn count_vowel_substrings(word: &[u8]) -> i64 {
    let n: usize = word.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if is_vowel(word[i]) {
            let mut has_a: bool = false;
            let mut has_e: bool = false;
            let mut has_i: bool = false;
            let mut has_o: bool = false;
            let mut has_u: bool = false;

            let mut j: usize = i;
            while j < n {
                let c: u8 = word[j];

                if !is_vowel(c) {
                    break;
                }

                if c == b'a' {
                    has_a = true;
                } else if c == b'e' {
                    has_e = true;
                } else if c == b'i' {
                    has_i = true;
                } else if c == b'o' {
                    has_o = true;
                } else if c == b'u' {
                    has_u = true;
                }

                if has_a && has_e && has_i && has_o && has_u {
                    ans += 1;
                }

                j += 1;
            }
        }

        i += 1;
    }

    ans
}
