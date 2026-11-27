pub fn remove_subfolders(folder: &[Vec<u8>]) -> Vec<Vec<u8>> {
    // Trie stored with flat adjacency lists.
    // head[node] is edge_index + 1, or 0 if there is no child.
    let mut head: Vec<usize> = Vec::new();
    let mut terminals: Vec<bool> = Vec::new();

    head.push(0);
    terminals.push(false);

    let mut edge_char: Vec<u8> = Vec::new();
    let mut edge_to: Vec<usize> = Vec::new();
    let mut edge_next: Vec<usize> = Vec::new();

    let mut f: usize = 0;
    while f < folder.len() {
        let s = &folder[f];
        let mut cur: usize = 0;
        let mut pos: usize = 0;
        let mut skipped: bool = false;

        while pos < s.len() {
            // A terminal node is a parent only when the next character is '/'.
            if terminals[cur] && s[pos] == b'/' {
                skipped = true;
                break;
            }

            let c = s[pos];
            let mut found: bool = false;
            let mut child: usize = 0;
            let mut e_plus = head[cur];

            while e_plus != 0 {
                let ei = e_plus - 1;
                if edge_char[ei] == c {
                    found = true;
                    child = edge_to[ei];
                    break;
                }
                e_plus = edge_next[ei];
            }

            if !found {
                let new_node = terminals.len();
                terminals.push(false);
                head.push(0);

                let new_edge = edge_char.len();
                edge_char.push(c);
                edge_to.push(new_node);
                edge_next.push(head[cur]);
                head[cur] = new_edge + 1;

                child = new_node;
            }

            cur = child;
            pos += 1;
        }

        if !skipped {
            terminals[cur] = true;
        }

        f += 1;
    }

    // Iterative DFS over the trie, producing paths in lexicographic order.
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut path: Vec<u8> = Vec::new();

    let mut stack_nodes: Vec<usize> = Vec::new();
    let mut stack_next_char: Vec<u8> = Vec::new();

    stack_nodes.push(0);
    stack_next_char.push(0);

    while stack_nodes.len() > 0 {
        let top = stack_nodes.len() - 1;
        let node = stack_nodes[top];
        let start = stack_next_char[top];

        // Output a terminal path once, on first visiting this node.
        if terminals[node] && start == 0 {
            let mut p: Vec<u8> = Vec::new();
            let mut i: usize = 0;
            while i < path.len() {
                p.push(path[i]);
                i += 1;
            }
            out.push(p);
        }

        let mut found: bool = false;
        let mut best_char: u8 = 255;
        let mut best_to: usize = 0;

        let mut e_plus = head[node];
        while e_plus != 0 {
            let ei = e_plus - 1;
            let c = edge_char[ei];

            // If this node is terminal, the '/' child represents subfolders.
            let mut eligible: bool = true;
            if terminals[node] && c == b'/' {
                eligible = false;
            }

            if eligible && c >= start {
                if !found || c < best_char {
                    found = true;
                    best_char = c;
                    best_to = edge_to[ei];
                }
            }

            e_plus = edge_next[ei];
        }

        if found {
            stack_next_char[top] = best_char + 1;
            path.push(best_char);
            stack_nodes.push(best_to);
            stack_next_char.push(0);
        } else {
            stack_nodes.pop();
            stack_next_char.pop();
            if path.len() > 0 {
                path.pop();
            }
        }
    }

    out
}
