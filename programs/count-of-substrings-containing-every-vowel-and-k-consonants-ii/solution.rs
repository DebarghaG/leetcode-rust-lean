fn is_vowel(c: u8) -> bool {
    c == b'a' || c == b'e' || c == b'i' || c == b'o' || c == b'u'
}

fn count_at_most(word: &[u8], maxc: i64) -> i64 {
    if maxc < 0 {
        return 0;
    }

    let n = word.len();

    let mut last_a: i64 = -1;
    let mut last_e: i64 = -1;
    let mut last_i: i64 = -1;
    let mut last_o: i64 = -1;
    let mut last_u: i64 = -1;

    let mut consonants: i64 = 0;
    let mut left: usize = 0;
    let mut total: i64 = 0;
    let mut right: usize = 0;

    while right < n {
        let c = word[right];

        if c == b'a' {
            last_a = right as i64;
        } else if c == b'e' {
            last_e = right as i64;
        } else if c == b'i' {
            last_i = right as i64;
        } else if c == b'o' {
            last_o = right as i64;
        } else if c == b'u' {
            last_u = right as i64;
        } else {
            consonants += 1;
        }

        while consonants > maxc {
            if !is_vowel(word[left]) {
                consonants -= 1;
            }
            left += 1;
        }

        let mut earliest_last = last_a;

        if last_e < earliest_last {
            earliest_last = last_e;
        }
        if last_i < earliest_last {
            earliest_last = last_i;
        }
        if last_o < earliest_last {
            earliest_last = last_o;
        }
        if last_u < earliest_last {
            earliest_last = last_u;
        }

        if earliest_last >= 0 {
            let left_i64 = left as i64;
            if earliest_last >= left_i64 {
                total += earliest_last - left_i64 + 1;
            }
        }

        right += 1;
    }

    total
}

pub fn count_of_substrings(word: &[u8], k: i64) -> i64 {
    let at_most_k = count_at_most(word, k);
    let at_most_k_minus_one = count_at_most(word, k - 1);
    at_most_k - at_most_k_minus_one
}
