fn find_child(
    head: &[i64],
    edge_to: &[i64],
    edge_next: &[i64],
    edge_ch: &[u8],
    node: usize,
    c: u8,
) -> i64 {
    let mut e = head[node];
    while e != -1 {
        let ei = e as usize;
        if edge_ch[ei] == c {
            return edge_to[ei];
        }
        e = edge_next[ei];
    }
    -1
}

pub fn count_prefix_suffix_pairs(words: &[Vec<u8>]) -> i64 {
    let n = words.len();

    let mut head: Vec<i64> = Vec::new();
    let mut edge_to: Vec<i64> = Vec::new();
    let mut edge_next: Vec<i64> = Vec::new();
    let mut edge_ch: Vec<u8> = Vec::new();
    let mut count: Vec<i64> = Vec::new();

    head.push(-1);
    count.push(0);

    let mut answer: i64 = 0;
    let mut wi: usize = 0;

    while wi < n {
        let word = &words[wi];
        let m = word.len();

        // Record trie nodes reached by each prefix of the current word.
        let mut prefix_nodes: Vec<i64> = Vec::new();
        prefix_nodes.push(0);

        let mut cur: i64 = 0;
        let mut i: usize = 0;
        while i < m {
            if cur != -1 {
                let nxt = find_child(
                    &head,
                    &edge_to,
                    &edge_next,
                    &edge_ch,
                    cur as usize,
                    word[i],
                );
                prefix_nodes.push(nxt);
                cur = nxt;
            } else {
                prefix_nodes.push(-1);
            }
            i += 1;
        }

        // Prefix function of the current word.
        let mut pi: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z < m {
            pi.push(0);
            z += 1;
        }

        let mut i2: usize = 1;
        let mut len: usize = 0;
        while i2 < m {
            if word[i2] == word[len] {
                len += 1;
                pi[i2] = len as i64;
                i2 += 1;
            } else {
                if len > 0 {
                    len = pi[len - 1] as usize;
                } else {
                    i2 += 1;
                }
            }
        }

        // The valid previous words must be equal to a border of the current word.
        let mut k: usize = m;
        while k > 0 {
            let node = prefix_nodes[k];
            if node != -1 {
                answer += count[node as usize];
            }
            k = pi[k - 1] as usize;
        }

        // Insert the current word only after counting, to enforce i < j.
        let mut node: usize = 0;
        let mut j: usize = 0;
        while j < m {
            let c = word[j];
            let found = find_child(&head, &edge_to, &edge_next, &edge_ch, node, c);

            if found == -1 {
                let new_node = count.len();
                let eidx = edge_to.len();

                edge_to.push(new_node as i64);
                edge_ch.push(c);
                edge_next.push(head[node]);

                head.push(-1);
                count.push(0);

                head[node] = eidx as i64;
                node = new_node;
            } else {
                node = found as usize;
            }

            j += 1;
        }

        count[node] += 1;
        wi += 1;
    }

    answer
}
