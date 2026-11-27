pub fn equal_digit_frequency(s: &[u8]) -> i64 {
    let n: usize = s.len();

    // Trie of all suffixes, stored as a flat array of child indices.
    // Each node has 10 possible digit children; -1 means absent.
    let mut children: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 10 {
        children.push(-1);
        i += 1;
    }

    let mut node_count: usize = 1;
    let mut answer: i64 = 0;

    let mut start: usize = 0;
    while start < n {
        let mut freq: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < 10 {
            freq.push(0);
            k += 1;
        }

        let mut distinct: i64 = 0;
        let mut max_freq: i64 = 0;
        let mut length: i64 = 0;
        let mut cur: usize = 0;

        let mut j: usize = start;
        while j < n {
            let digit: usize = (s[j] - b'0') as usize;

            let old: i64 = freq[digit];
            freq[digit] = old + 1;
            if old == 0 {
                distinct += 1;
            }

            let now: i64 = freq[digit];
            if now > max_freq {
                max_freq = now;
            }

            length += 1;
            let valid: bool = max_freq * distinct == length;

            let base: usize = cur * 10 + digit;
            let child: i64 = children[base];

            if child == -1 {
                let new_id: usize = node_count;
                children[base] = new_id as i64;

                let mut p: usize = 0;
                while p < 10 {
                    children.push(-1);
                    p += 1;
                }

                node_count += 1;

                if valid {
                    answer += 1;
                }

                cur = new_id;
            } else {
                cur = child as usize;
            }

            j += 1;
        }

        start += 1;
    }

    answer
}
