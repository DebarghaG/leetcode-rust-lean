pub fn longest_cycle(edges: &[i64]) -> i64 {
    let n = edges.len();

    let mut state: Vec<i64> = Vec::new();
    let mut dist: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < n {
        state.push(0);
        dist.push(0);
        k += 1;
    }

    let mut ans: i64 = -1;
    let mut i: usize = 0;

    while i < n {
        if state[i] != 0 {
            i += 1;
            continue;
        }

        let mut cur: usize = i;
        let mut steps: i64 = 0;

        loop {
            if state[cur] != 0 {
                break;
            }

            state[cur] = 1;
            dist[cur] = steps;

            let nxt = edges[cur];
            if nxt == -1 {
                break;
            }

            cur = nxt as usize;
            steps += 1;
        }

        if state[cur] == 1 && edges[cur] != -1 {
            let cyc = steps - dist[cur];
            if cyc > ans {
                ans = cyc;
            }
        }

        let mut p: usize = i;
        loop {
            if state[p] != 1 {
                break;
            }

            state[p] = 2;

            let nxt = edges[p];
            if nxt == -1 {
                break;
            }

            p = nxt as usize;
        }

        i += 1;
    }

    ans
}
