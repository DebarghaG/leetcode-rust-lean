pub fn minimum_semesters(n: i64, relations: &[Vec<i64>]) -> i64 {
    let nu: usize = n as usize;

    let mut indeg: Vec<i64> = Vec::new();
    let mut head: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i <= nu {
        indeg.push(0);
        head.push(-1);
        i += 1;
    }

    let mut to: Vec<i64> = Vec::new();
    let mut next: Vec<i64> = Vec::new();
    let mut edge_count: i64 = 0;

    let mut r: usize = 0;
    while r < relations.len() {
        let a: i64 = relations[r][0];
        let b: i64 = relations[r][1];
        let ai: usize = a as usize;
        let bi: usize = b as usize;

        to.push(b);
        next.push(head[ai]);
        head[ai] = edge_count;
        edge_count += 1;

        indeg[bi] += 1;
        r += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    let mut c: i64 = 1;
    while c <= n {
        let ci: usize = c as usize;
        if indeg[ci] == 0 {
            queue.push(c);
        }
        c += 1;
    }

    let mut semesters: i64 = 0;
    let mut processed: i64 = 0;
    let mut q_start: usize = 0;

    while q_start < queue.len() {
        semesters += 1;
        let level_end: usize = queue.len();

        while q_start < level_end {
            let u: i64 = queue[q_start];
            q_start += 1;
            processed += 1;

            let ui: usize = u as usize;
            let mut e: i64 = head[ui];

            while e != -1 {
                let v: i64 = to[e as usize];
                let vi: usize = v as usize;

                indeg[vi] -= 1;
                if indeg[vi] == 0 {
                    queue.push(v);
                }

                e = next[e as usize];
            }
        }
    }

    if processed == n {
        semesters
    } else {
        -1
    }
}
