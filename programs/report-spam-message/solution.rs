pub fn report_spam(message: &[Vec<u8>], bannedWords: &[Vec<u8>]) -> bool {
    let mut head: Vec<usize> = Vec::new();
    let mut next_edge: Vec<usize> = Vec::new();
    let mut edge_char: Vec<u8> = Vec::new();
    let mut edge_to: Vec<usize> = Vec::new();
    let mut is_end: Vec<bool> = Vec::new();

    head.push(0);
    is_end.push(false);

    let mut i = 0usize;
    while i < bannedWords.len() {
        let word = &bannedWords[i];
        let mut node = 0usize;
        let mut k = 0usize;

        while k < word.len() {
            let c = word[k];
            let mut link = head[node];
            let mut found = false;
            let mut child = 0usize;

            while link != 0 {
                let e = link - 1;
                if edge_char[e] == c {
                    child = edge_to[e];
                    found = true;
                    break;
                }
                link = next_edge[e];
            }

            if !found {
                child = head.len();
                head.push(0);
                is_end.push(false);

                let e = edge_char.len();
                edge_char.push(c);
                edge_to.push(child);
                next_edge.push(head[node]);
                head[node] = e + 1;
            }

            node = child;
            k += 1;
        }

        is_end[node] = true;
        i += 1;
    }

    let mut count: i64 = 0;
    let mut mi = 0usize;

    while mi < message.len() {
        let word = &message[mi];
        let mut node = 0usize;
        let mut ok = true;
        let mut k = 0usize;

        while k < word.len() {
            let c = word[k];
            let mut link = head[node];
            let mut found = false;
            let mut child = 0usize;

            while link != 0 {
                let e = link - 1;
                if edge_char[e] == c {
                    child = edge_to[e];
                    found = true;
                    break;
                }
                link = next_edge[e];
            }

            if !found {
                ok = false;
                break;
            }

            node = child;
            k += 1;
        }

        if ok && is_end[node] {
            count += 1;
            if count >= 2 {
                return true;
            }
        }

        mi += 1;
    }

    false
}
