fn highest_power(x: i64) -> i64 {
    let mut p: i64 = 1;
    while x / p >= 10 {
        p = p * 10;
    }
    p
}

pub fn longest_common_prefix(arr1: &[i64], arr2: &[i64]) -> i64 {
    let mut trie: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < 10 {
        trie.push(-1);
        i += 1;
    }

    let mut a: usize = 0;
    while a < arr1.len() {
        let x = arr1[a];
        let mut p = highest_power(x);
        let mut cur: i64 = 0;

        while p > 0 {
            let digit = (x / p) % 10;
            let pos = (cur * 10 + digit) as usize;
            let child = trie[pos];

            if child < 0 {
                let new_idx = (trie.len() / 10) as i64;

                let mut k: usize = 0;
                while k < 10 {
                    trie.push(-1);
                    k += 1;
                }

                trie[pos] = new_idx;
                cur = new_idx;
            } else {
                cur = child;
            }

            p = p / 10;
        }

        a += 1;
    }

    let mut best: i64 = 0;

    let mut b: usize = 0;
    while b < arr2.len() {
        let y = arr2[b];
        let mut p = highest_power(y);
        let mut cur: i64 = 0;
        let mut len: i64 = 0;

        while p > 0 {
            let digit = (y / p) % 10;
            let pos = (cur * 10 + digit) as usize;
            let child = trie[pos];

            if child < 0 {
                break;
            }

            cur = child;
            len += 1;
            p = p / 10;
        }

        if len > best {
            best = len;
        }

        b += 1;
    }

    best
}
