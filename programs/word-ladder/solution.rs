pub fn ladder_length(beginWord: &[u8], endWord: &[u8], wordList: &[Vec<u8>]) -> i64 {
    if bytes_equal(beginWord, endWord) {
        return 1;
    }

    let n: usize = wordList.len();

    // Locate the end word in the dictionary (sentinel n means "absent").
    let mut end_index: usize = n;
    let mut i: usize = 0;
    while i < n {
        if word_equals_bytes(wordList, i, endWord) {
            if end_index == n {
                end_index = i;
            }
        }
        i += 1;
    }

    if end_index == n {
        return 0;
    }

    // dist[j] for words; dist[n] for the virtual begin node.
    let mut dist: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= n {
        dist.push(-1);
        k += 1;
    }

    let mut queue: Vec<usize> = Vec::new();
    dist[n] = 1;
    queue.push(n);

    let mut head: usize = 0;
    while head < queue.len() {
        let cur: usize = queue[head];
        head += 1;
        let base: i64 = dist[cur];

        let mut j: usize = 0;
        while j < n {
            if dist[j] < 0 {
                let mut adjacent: bool = false;
                if cur == n {
                    adjacent = one_diff_begin(beginWord, wordList, j);
                } else {
                    adjacent = one_diff_words(wordList, cur, j);
                }
                if adjacent {
                    dist[j] = base + 1;
                    queue.push(j);
                }
            }
            j += 1;
        }
    }

    let d: i64 = dist[end_index];
    if d < 0 {
        return 0;
    }
    d
}

fn bytes_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    let mut eq: bool = true;
    while i < a.len() {
        if a[i] != b[i] {
            eq = false;
        }
        i += 1;
    }
    eq
}

fn word_equals_bytes(words: &[Vec<u8>], idx: usize, b: &[u8]) -> bool {
    let w = &words[idx];
    if w.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    let mut eq: bool = true;
    while i < w.len() {
        if w[i] != b[i] {
            eq = false;
        }
        i += 1;
    }
    eq
}

fn one_diff_begin(begin: &[u8], words: &[Vec<u8>], idx: usize) -> bool {
    let w = &words[idx];
    if begin.len() != w.len() {
        return false;
    }
    let mut diff: i64 = 0;
    let mut i: usize = 0;
    while i < begin.len() {
        if begin[i] != w[i] {
            diff += 1;
        }
        i += 1;
    }
    diff == 1
}

fn one_diff_words(words: &[Vec<u8>], a: usize, b: usize) -> bool {
    let wa = &words[a];
    let wb = &words[b];
    if wa.len() != wb.len() {
        return false;
    }
    let mut diff: i64 = 0;
    let mut i: usize = 0;
    while i < wa.len() {
        if wa[i] != wb[i] {
            diff += 1;
        }
        i += 1;
    }
    diff == 1
}
