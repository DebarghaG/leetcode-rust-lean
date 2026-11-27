fn new_row() -> Vec<i64> {
    let mut row: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        row.push(-1);
        k += 1;
    }
    row
}

pub fn find_substring(s: &[u8], words: &[Vec<u8>]) -> Vec<i64> {
    let mut answer: Vec<i64> = Vec::new();
    let nw: usize = words.len();

    if nw == 0 || s.len() == 0 {
        return answer;
    }

    let wl: usize = words[0].len();
    if wl == 0 {
        return answer;
    }

    let total: usize = nw * wl;
    if total > s.len() {
        return answer;
    }

    let mut check_i: usize = 0;
    while check_i < nw {
        if words[check_i].len() != wl {
            return answer;
        }
        check_i += 1;
    }

    let mut children: Vec<Vec<i64>> = Vec::new();
    children.push(new_row());

    let mut term_id: Vec<i64> = Vec::new();
    term_id.push(-1);

    let mut required: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < nw {
        let word = &words[i];
        let mut node: usize = 0;
        let mut j: usize = 0;

        while j < wl {
            let c: usize = (word[j] - b'a') as usize;
            let mut next: i64 = children[node][c];

            if next == -1 {
                let new_index: i64 = children.len() as i64;
                children.push(new_row());
                term_id.push(-1);
                children[node][c] = new_index;
                next = new_index;
            }

            node = next as usize;
            j += 1;
        }

        let id: i64 = term_id[node];
        if id == -1 {
            let new_id: i64 = required.len() as i64;
            term_id[node] = new_id;
            required.push(1);
        } else {
            let idx: usize = id as usize;
            required[idx] = required[idx] + 1;
        }

        i += 1;
    }

    let unique_count: usize = required.len();
    let limit: usize = s.len() - total;
    let mut start: usize = 0;

    while start <= limit {
        let mut seen: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z < unique_count {
            seen.push(0);
            z += 1;
        }

        let mut valid: bool = true;
        let mut k: usize = 0;

        while k < nw {
            let pos: usize = start + k * wl;
            let mut node: usize = 0;
            let mut j: usize = 0;
            let mut found: bool = true;

            while j < wl {
                if found {
                    let c: usize = (s[pos + j] - b'a') as usize;
                    let child: i64 = children[node][c];

                    if child == -1 {
                        found = false;
                    } else {
                        node = child as usize;
                    }
                }
                j += 1;
            }

            if !found {
                valid = false;
                k = nw;
            } else {
                let id: i64 = term_id[node];

                if id == -1 {
                    valid = false;
                    k = nw;
                } else {
                    let idx: usize = id as usize;
                    seen[idx] = seen[idx] + 1;

                    if seen[idx] > required[idx] {
                        valid = false;
                        k = nw;
                    } else {
                        k += 1;
                    }
                }
            }
        }

        if valid {
            answer.push(start as i64);
        }

        start += 1;
    }

    answer
}
