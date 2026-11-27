fn is_vowel(c: u8) -> bool {
    c == b'a' || c == b'e' || c == b'i' || c == b'o' || c == b'u'
}

pub fn count_of_substrings(word: &[u8], k: i64) -> i64 {
    let n = word.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut consonants: i64 = 0;
        let mut has_a: bool = false;
        let mut has_e: bool = false;
        let mut has_i: bool = false;
        let mut has_o: bool = false;
        let mut has_u: bool = false;

        let mut j: usize = i;
        while j < n {
            let c = word[j];

            if is_vowel(c) {
                if c == b'a' {
                    has_a = true;
                } else if c == b'e' {
                    has_e = true;
                } else if c == b'i' {
                    has_i = true;
                } else if c == b'o' {
                    has_o = true;
                } else {
                    has_u = true;
                }
            } else {
                consonants = consonants + 1;
            }

            if consonants > k {
                break;
            }

            if consonants == k && has_a && has_e && has_i && has_o && has_u {
                total = total + 1;
            }

            j = j + 1;
        }

        i = i + 1;
    }

    total
}
