pub fn maximize_sum_of_weights(edges: &[Vec<i64>], k: i64) -> i64 {
    let n = edges.len() + 1;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        adj.push(Vec::new());
        i += 1;
    }

    i = 0;
    while i < edges.len() {
        let u = edges[i][0] as usize;
        let v = edges[i][1] as usize;
        let w = edges[i][2];

        adj[u].push(v as i64);
        adj[u].push(w);
        adj[v].push(u as i64);
        adj[v].push(w);

        i += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut dp0: Vec<i64> = Vec::new();
    let mut dp1: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        parent.push(-1);
        dp0.push(0);
        dp1.push(0);
        i += 1;
    }
    parent[0] = -2;

    let mut order: Vec<i64> = Vec::new();
    let mut queue: Vec<i64> = Vec::new();
    queue.push(0);

    let mut head = 0usize;
    while head < queue.len() {
        let u_i = queue[head];
        head += 1;
        order.push(u_i);

        let u = u_i as usize;
        let mut p = 0usize;
        let alen = adj[u].len();
        while p < alen {
            let v_i = adj[u][p];
            let v = v_i as usize;

            if parent[v] == -1 {
                parent[v] = u_i;
                queue.push(v_i);
            }

            p += 2;
        }
    }

    let cap_k = if k > 0 { k as usize } else { 0 };
    let cap_parent = if k > 1 { (k - 1) as usize } else { 0 };

    let mut idx = order.len();
    while idx > 0 {
        idx -= 1;

        let u_i = order[idx];
        let u = u_i as usize;

        let mut base = 0i64;
        let mut heap: Vec<i64> = Vec::new();

        let mut p = 0usize;
        let alen = adj[u].len();
        while p < alen {
            let v_i = adj[u][p];
            let v = v_i as usize;

            if parent[v] == u_i {
                let w = adj[u][p + 1];
                base += dp0[v];

                let gain = w + dp1[v] - dp0[v];
                if gain > 0 {
                    if heap.len() < cap_k {
                        heap.push(gain);
                        let mut pos = heap.len() - 1;

                        while pos > 0 {
                            let par = (pos - 1) / 2;
                            if heap[pos] < heap[par] {
                                let tmp = heap[pos];
                                heap[pos] = heap[par];
                                heap[par] = tmp;
                                pos = par;
                            } else {
                                break;
                            }
                        }
                    } else if cap_k > 0 && gain > heap[0] {
                        heap[0] = gain;

                        let mut pos = 0usize;
                        let hn = heap.len();

                        while pos < hn {
                            let l = 2 * pos + 1;
                            if l >= hn {
                                break;
                            }

                            let mut smallest = pos;
                            if heap[l] < heap[smallest] {
                                smallest = l;
                            }

                            let r = l + 1;
                            if r < hn && heap[r] < heap[smallest] {
                                smallest = r;
                            }

                            if smallest == pos {
                                break;
                            }

                            let tmp = heap[pos];
                            heap[pos] = heap[smallest];
                            heap[smallest] = tmp;
                            pos = smallest;
                        }
                    }
                }
            }

            p += 2;
        }

        let mut hs = 0i64;
        let mut hi = 0usize;
        while hi < heap.len() {
            hs += heap[hi];
            hi += 1;
        }

        dp0[u] = base + hs;

        if heap.len() <= cap_parent {
            dp1[u] = base + hs;
        } else {
            dp1[u] = base + hs - heap[0];
        }
    }

    dp0[0]
}
