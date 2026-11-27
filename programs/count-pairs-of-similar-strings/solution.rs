pub fn similar_pairs(words: &[Vec<u8>]) -> i64 {
    let n = words.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            if are_similar(&words[i], &words[j]) {
                count = count + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    count
}

fn are_similar(a: &[u8], b: &[u8]) -> bool {
    let mut c: usize = 0;

    while c < 26 {
        let target: u8 = b'a' + (c as u8);
        let in_a = contains_byte(a, target);
        let in_b = contains_byte(b, target);

        if in_a != in_b {
            return false;
        }

        c = c + 1;
    }

    true
}

fn contains_byte(s: &[u8], target: u8) -> bool {
    let mut i: usize = 0;

    while i < s.len() {
        if s[i] == target {
            return true;
        }
        i = i + 1;
    }

    false
}
