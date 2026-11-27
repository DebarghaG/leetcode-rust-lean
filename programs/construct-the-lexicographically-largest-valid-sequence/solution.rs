pub fn construct_distanced_sequence(n: i64) -> Vec<i64> {
    let m = (2 * n - 1) as usize;
    let n_usize = n as usize;

    let mut seq: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        seq.push(0);
        i += 1;
    }

    let mut used: Vec<bool> = Vec::new();
    let mut j = 0;
    while j <= n_usize {
        used.push(false);
        j += 1;
    }

    let mut stack_pos: Vec<usize> = Vec::new();
    let mut stack_next: Vec<i64> = Vec::new();
    let mut stack_choice: Vec<i64> = Vec::new();

    let mut first = 0;
    while first < m && seq[first] != 0 {
        first += 1;
    }
    stack_pos.push(first);
    stack_next.push(n);
    stack_choice.push(0);

    while stack_pos.len() > 0 {
        let idx = stack_pos.len() - 1;
        let pos = stack_pos[idx];

        if pos == m {
            return seq;
        }

        let mut cand = stack_next[idx];
        let mut chosen = 0;

        while cand >= 1 {
            let ci = cand as usize;
            let mut ok = false;

            if !used[ci] && seq[pos] == 0 {
                if cand == 1 {
                    ok = true;
                } else {
                    let p2 = pos + cand as usize;
                    if p2 < m && seq[p2] == 0 {
                        ok = true;
                    }
                }
            }

            if ok {
                chosen = cand;
                break;
            }
            cand -= 1;
        }

        if chosen == 0 {
            let ch = stack_choice[idx];
            let mut parent_pos = 0;
            if idx > 0 {
                parent_pos = stack_pos[idx - 1];
            }

            let _ = stack_pos.pop();
            let _ = stack_next.pop();
            let _ = stack_choice.pop();

            if ch > 0 {
                seq[parent_pos] = 0;
                if ch > 1 {
                    let p2 = parent_pos + ch as usize;
                    seq[p2] = 0;
                }
                used[ch as usize] = false;
            }
        } else {
            seq[pos] = chosen;
            if chosen > 1 {
                let p2 = pos + chosen as usize;
                seq[p2] = chosen;
            }
            used[chosen as usize] = true;
            stack_next[idx] = chosen - 1;

            let mut np = pos + 1;
            while np < m && seq[np] != 0 {
                np += 1;
            }

            stack_pos.push(np);
            stack_next.push(n);
            stack_choice.push(chosen);
        }
    }

    seq
}
