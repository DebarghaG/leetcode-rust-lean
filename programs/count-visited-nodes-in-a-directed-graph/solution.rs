pub fn count_visited_nodes(edges: &[i64]) -> Vec<i64> {
    let n = edges.len();

    let mut state: Vec<i64> = Vec::new();
    let mut ans: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        state.push(0);
        ans.push(0);
        i += 1;
    }

    let mut start = 0;
    while start < n {
        if state[start] == 0 {
            let mut path: Vec<usize> = Vec::new();
            let mut cur = start;

            while state[cur] == 0 {
                state[cur] = 1;
                path.push(cur);
                cur = edges[cur] as usize;
            }

            if state[cur] == 2 {
                let mut k = path.len();
                while k > 0 {
                    k -= 1;

                    let node = path[k];
                    let next_node = if k + 1 < path.len() {
                        path[k + 1]
                    } else {
                        cur
                    };

                    ans[node] = ans[next_node] + 1;
                    state[node] = 2;
                }
            } else {
                let mut idx = 0;
                while idx < path.len() {
                    if path[idx] == cur {
                        break;
                    }
                    idx += 1;
                }

                let cycle_len = (path.len() - idx) as i64;

                let mut j = idx;
                while j < path.len() {
                    let node = path[j];
                    ans[node] = cycle_len;
                    state[node] = 2;
                    j += 1;
                }

                let mut k = idx;
                while k > 0 {
                    k -= 1;

                    let node = path[k];
                    let next_node = path[k + 1];

                    ans[node] = ans[next_node] + 1;
                    state[node] = 2;
                }
            }
        }

        start += 1;
    }

    ans
}
