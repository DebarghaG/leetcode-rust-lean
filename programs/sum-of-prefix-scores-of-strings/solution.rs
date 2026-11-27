pub fn sum_prefix_scores(words: &[Vec<u8>]) -> Vec<i64> {
    let n = words.len();

    // Flattened trie representation:
    // children[node * 26 + letter] = child node index, or -1 if absent.
    let mut children: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    // Create root node 0.
    let mut k: i64 = 0;
    while k < 26 {
        children.push(-1);
        k += 1;
    }
    counts.push(0);

    // Insert all words into the trie and count prefixes.
    let mut i: usize = 0;
    while i < n {
        let mut node: i64 = 0;
        let len = words[i].len();
        let mut j: usize = 0;

        while j < len {
            let byte_i64: i64 = words[i][j] as i64;
            let letter_i64: i64 = byte_i64 - 97;
            let letter: usize = letter_i64 as usize;

            let node_usize: usize = node as usize;
            let pos: usize = node_usize * 26 + letter;
            let child: i64 = children[pos];

            if child == -1 {
                let new_node: i64 = counts.len() as i64;
                children[pos] = new_node;

                let mut t: i64 = 0;
                while t < 26 {
                    children.push(-1);
                    t += 1;
                }
                counts.push(0);

                node = new_node;
            } else {
                node = child;
            }

            let node_idx: usize = node as usize;
            counts[node_idx] = counts[node_idx] + 1;

            j += 1;
        }

        i += 1;
    }

    // For each word, sum the counts along its trie path.
    let mut answer: Vec<i64> = Vec::new();
    let mut i2: usize = 0;

    while i2 < n {
        let mut node: i64 = 0;
        let mut sum: i64 = 0;
        let len = words[i2].len();
        let mut j2: usize = 0;

        while j2 < len {
            let byte_i64: i64 = words[i2][j2] as i64;
            let letter_i64: i64 = byte_i64 - 97;
            let letter: usize = letter_i64 as usize;

            let node_usize: usize = node as usize;
            let pos: usize = node_usize * 26 + letter;
            let child: i64 = children[pos];

            node = child;

            let node_idx: usize = node as usize;
            sum = sum + counts[node_idx];

            j2 += 1;
        }

        answer.push(sum);
        i2 += 1;
    }

    answer
}
