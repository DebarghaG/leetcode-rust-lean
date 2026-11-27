pub fn find_maximum_xor(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    // Binary trie stored in a single vector.
    // For node index `v`, its children are stored at 2*v and 2*v+1.
    // -1 means the child does not exist.
    let mut trie: Vec<i64> = Vec::new();
    trie.push(-1);
    trie.push(-1);

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        let mut node: usize = 0;
        let mut k: usize = 31;

        while k > 0 {
            k -= 1;
            let bit = ((x >> k) & 1) as usize;
            let left = node * 2;
            let right = left + 1;

            if bit == 0 {
                let next = trie[left];
                if next == -1 {
                    let new_idx = (trie.len() / 2) as i64;
                    trie.push(-1);
                    trie.push(-1);
                    trie[left] = new_idx;
                    node = new_idx as usize;
                } else {
                    node = next as usize;
                }
            } else {
                let next = trie[right];
                if next == -1 {
                    let new_idx = (trie.len() / 2) as i64;
                    trie.push(-1);
                    trie.push(-1);
                    trie[right] = new_idx;
                    node = new_idx as usize;
                } else {
                    node = next as usize;
                }
            }
        }

        i += 1;
    }

    let mut best: i64 = 0;
    i = 0;

    while i < n {
        let x = nums[i];
        let mut node: usize = 0;
        let mut cur: i64 = 0;
        let mut k: usize = 31;

        while k > 0 {
            k -= 1;
            let bit = ((x >> k) & 1) as usize;
            let left = node * 2;
            let right = left + 1;

            if bit == 0 {
                let opposite = trie[right];
                if opposite != -1 {
                    cur |= 1i64 << k;
                    node = opposite as usize;
                } else {
                    node = trie[left] as usize;
                }
            } else {
                let opposite = trie[left];
                if opposite != -1 {
                    cur |= 1i64 << k;
                    node = opposite as usize;
                } else {
                    node = trie[right] as usize;
                }
            }
        }

        if cur > best {
            best = cur;
        }

        i += 1;
    }

    best
}
