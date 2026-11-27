pub fn longest_valid_substring(word: &[u8], forbidden: &[Vec<u8>]) -> i64 {
    let mut head: Vec<i64> = Vec::new();
    let mut edge_to: Vec<i64> = Vec::new();
    let mut edge_next: Vec<i64> = Vec::new();
    let mut edge_ch: Vec<u8> = Vec::new();
    let mut terminal: Vec<i64> = Vec::new();

    head.push(-1);
    terminal.push(0);

    let mut max_len: usize = 0;
    let mut fi: usize = 0;
    while fi < forbidden.len() {
        let pat = &forbidden[fi];
        if pat.len() > max_len {
            max_len = pat.len();
        }

        let mut node: i64 = 0;
        let mut pi: usize = pat.len();
        while pi > 0 {
            pi -= 1;
            let c = pat[pi];

            let mut e = head[node as usize];
            let mut found: i64 = -1;
            while e != -1 {
                if edge_ch[e as usize] == c {
                    found = edge_to[e as usize];
                    e = -1;
                } else {
                    e = edge_next[e as usize];
                }
            }

            if found == -1 {
                let new_node = head.len() as i64;
                head.push(-1);
                terminal.push(0);

                let new_edge = edge_to.len() as i64;
                edge_to.push(new_node);
                edge_ch.push(c);
                edge_next.push(head[node as usize]);
                head[node as usize] = new_edge;

                node = new_node;
            } else {
                node = found;
            }
        }

        terminal[node as usize] = 1;
        fi += 1;
    }

    let n = word.len();
    let mut left: usize = 0;
    let mut ans: i64 = 0;
    let mut r: usize = 0;

    while r < n {
        let mut node: i64 = 0;
        let mut l: usize = 1;

        while l <= max_len && l <= r + 1 {
            let c = word[r + 1 - l];

            let mut e = head[node as usize];
            let mut found: i64 = -1;
            while e != -1 {
                if edge_ch[e as usize] == c {
                    found = edge_to[e as usize];
                    e = -1;
                } else {
                    e = edge_next[e as usize];
                }
            }

            if found == -1 {
                break;
            }

            node = found;

            if terminal[node as usize] == 1 {
                let start = r + 1 - l;
                let cand = start + 1;
                if cand > left {
                    left = cand;
                }
                break;
            }

            l += 1;
        }

        let cur = (r as i64) - (left as i64) + 1;
        if cur > ans {
            ans = cur;
        }

        r += 1;
    }

    ans
}
