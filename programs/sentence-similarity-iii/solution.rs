fn count_words(s: &[u8]) -> usize {
    if s.len() == 0 {
        return 0;
    }
    let mut count = 1usize;
    let mut i = 0usize;
    while i < s.len() {
        if s[i] == b' ' {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

fn word_start(s: &[u8], idx: usize) -> usize {
    if idx == 0 {
        return 0;
    }
    let mut i = 0usize;
    let mut cur = 0usize;
    while i < s.len() {
        if s[i] == b' ' {
            cur = cur + 1;
            if cur == idx {
                return i + 1;
            }
        }
        i = i + 1;
    }
    s.len()
}

fn word_end(s: &[u8], idx: usize) -> usize {
    let start = word_start(s, idx);
    let mut i = start;
    while i < s.len() && s[i] != b' ' {
        i = i + 1;
    }
    i
}

fn word_equal(s1: &[u8], i: usize, s2: &[u8], j: usize) -> bool {
    let a = word_start(s1, i);
    let b = word_end(s1, i);
    let c = word_start(s2, j);
    let d = word_end(s2, j);

    let len1 = b - a;
    let len2 = d - c;

    if len1 != len2 {
        return false;
    }

    let mut k = 0usize;
    while k < len1 {
        if s1[a + k] != s2[c + k] {
            return false;
        }
        k = k + 1;
    }

    true
}

pub fn are_sentences_similar(sentence1: &[u8], sentence2: &[u8]) -> bool {
    let n1 = count_words(sentence1);
    let n2 = count_words(sentence2);

    let mut short_s = sentence1;
    let mut long_s = sentence2;
    let mut m = n1;
    let mut n = n2;

    if n1 > n2 {
        short_s = sentence2;
        long_s = sentence1;
        m = n2;
        n = n1;
    }

    let mut p = 0usize;
    while p < m {
        if !word_equal(short_s, p, long_s, p) {
            break;
        }
        p = p + 1;
    }

    if p == m {
        return true;
    }

    let rem = m - p;
    let long_start = n - rem;

    let mut k = 0usize;
    while k < rem {
        if !word_equal(short_s, p + k, long_s, long_start + k) {
            return false;
        }
        k = k + 1;
    }

    true
}
