pub fn min_valid_strings(words: &[Vec<u8>], target: &[u8]) -> i64 {
    let n = target.len();
    if n == 0 {
        return 0;
    }

    // Build a trie (as a flat Vec<i64>, 26 children per node).
    let mut trie: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < 26 {
        trie.push(-1);
        k += 1;
    }

    let mut node_count: usize = 1;
    let mut w = 0;
    while w < words.len() {
        let wlen = words[w].len();
        let mut node: usize = 0;
        let mut p = 0;
        while p < wlen {
            let c = words[w][p];
            let idx = (c - b'a') as usize;
            let slot = node * 26 + idx;
            let nxt = trie[slot];

            if nxt == -1 {
                let new_id = node_count as i64;
                trie[slot] = new_id;

                let mut kk = 0;
                while kk < 26 {
                    trie.push(-1);
                    kk += 1;
                }

                node_count += 1;
                node = new_id as usize;
            } else {
                node = nxt as usize;
            }

            p += 1;
        }
        w += 1;
    }

    // For each position i in target, compute the longest prefix-match length.
    let mut maxlen: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        let mut node: usize = 0;
        let mut j = i;
        let mut len: i64 = 0;

        while j < n {
            let c = target[j];
            let idx = (c - b'a') as usize;
            let slot = node * 26 + idx;
            let nxt = trie[slot];

            if nxt == -1 {
                break;
            }

            node = nxt as usize;
            len += 1;
            j += 1;
        }

        maxlen.push(len);
        i += 1;
    }

    // Greedy jump-game style minimum number of segments.
    let n_i = n as i64;
    let mut steps: i64 = 0;
    let mut cur_end: i64 = 0;
    let mut farthest: i64 = 0;
    let mut pos: i64 = 0;
    let mut possible: bool = true;

    while cur_end < n_i && possible {
        steps += 1;

        let mut scan = pos;
        while scan <= cur_end && scan < n_i {
            let idx = scan as usize;
            let reach = scan + maxlen[idx];
            if reach > farthest {
                farthest = reach;
            }
            scan += 1;
        }
        pos = scan;

        if farthest <= cur_end {
            possible = false;
        } else {
            cur_end = farthest;
        }
    }

    if !possible {
        return -1;
    }

    steps
}
