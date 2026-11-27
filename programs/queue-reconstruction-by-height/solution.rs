pub fn reconstruct_queue(people: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = people.len();

    let mut used: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n {
        used.push(false);
        i += 1;
    }

    let mut ordered: Vec<i64> = Vec::new();
    let mut cnt = 0;
    while cnt < n {
        let mut best: usize = n;
        let mut j = 0;
        while j < n {
            if !used[j] {
                if best == n {
                    best = j;
                } else {
                    let h_j = people[j][0];
                    let h_b = people[best][0];
                    let k_j = people[j][1];
                    let k_b = people[best][1];
                    if h_j > h_b || (h_j == h_b && k_j < k_b) {
                        best = j;
                    }
                }
            }
            j += 1;
        }

        used[best] = true;
        ordered.push(best as i64);
        cnt += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    let mut oi = 0;
    while oi < n {
        let idx_i = ordered[oi];
        let idx = idx_i as usize;
        let pos = people[idx][1] as usize;

        let mut newq: Vec<i64> = Vec::new();
        let qlen = queue.len();
        let mut inserted = false;
        let mut qi = 0;
        while qi < qlen {
            if qi == pos {
                newq.push(idx_i);
                inserted = true;
            }
            newq.push(queue[qi]);
            qi += 1;
        }

        if !inserted {
            newq.push(idx_i);
        }

        queue = newq;
        oi += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut qi = 0;
    while qi < n {
        let idx = queue[qi] as usize;
        let mut row: Vec<i64> = Vec::new();
        row.push(people[idx][0]);
        row.push(people[idx][1]);
        out.push(row);
        qi += 1;
    }

    out
}
