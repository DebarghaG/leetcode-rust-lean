fn heap_push(heap: &mut Vec<i64>, x: i64) {
    heap.push(x);
    let mut i = heap.len() - 1;
    let mut stop = false;
    while i > 0 && !stop {
        let p = (i - 1) / 2;
        if heap[p] <= heap[i] {
            stop = true;
        } else {
            let tmp = heap[p];
            heap[p] = heap[i];
            heap[i] = tmp;
            i = p;
        }
    }
}

fn heap_pop(heap: &mut Vec<i64>) -> i64 {
    let len = heap.len();
    let res = heap[0];
    let last = heap[len - 1];
    heap.pop();

    let new_len = heap.len();
    if new_len > 0 {
        heap[0] = last;
        let mut i = 0usize;
        let mut stop = false;
        while i < new_len && !stop {
            let left = 2 * i + 1;
            if left >= new_len {
                stop = true;
            } else {
                let mut smallest = left;
                let right = left + 1;
                if right < new_len && heap[right] < heap[left] {
                    smallest = right;
                }

                if heap[i] <= heap[smallest] {
                    stop = true;
                } else {
                    let tmp = heap[i];
                    heap[i] = heap[smallest];
                    heap[smallest] = tmp;
                    i = smallest;
                }
            }
        }
    }

    res
}

pub fn count_restricted_paths(n: i64, edges: &[Vec<i64>]) -> i64 {
    let n_us = n as usize;
    let base = n + 1;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i <= n_us {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut e = 0usize;
    while e < edges.len() {
        let u = edges[e][0] as usize;
        let v = edges[e][1] as usize;
        let w = edges[e][2];

        adj[u].push(v as i64);
        adj[u].push(w);
        adj[v].push(u as i64);
        adj[v].push(w);

        e += 1;
    }

    let inf: i64 = 1000000000000;
    let mut dist: Vec<i64> = Vec::new();
    i = 0;
    while i <= n_us {
        dist.push(inf);
        i += 1;
    }
    dist[n_us] = 0;

    let mut visited: Vec<bool> = Vec::new();
    i = 0;
    while i <= n_us {
        visited.push(false);
        i += 1;
    }

    let mut heap: Vec<i64> = Vec::new();
    heap_push(&mut heap, n_us as i64);

    while heap.len() > 0 {
        let key = heap_pop(&mut heap);
        let u = (key % base) as usize;

        if !visited[u] {
            visited[u] = true;
            let d = dist[u];
            let row = &adj[u];

            let mut j = 0usize;
            while j < row.len() {
                let v = row[j] as usize;
                let w = row[j + 1];

                if !visited[v] {
                    let nd = d + w;
                    if nd < dist[v] {
                        dist[v] = nd;
                        heap_push(&mut heap, nd * base + v as i64);
                    }
                }

                j += 2;
            }
        }
    }

    let mut order: Vec<i64> = Vec::new();
    i = 1;
    while i <= n_us {
        order.push(dist[i] * base + i as i64);
        i += 1;
    }
    order.sort();

    let mut dp: Vec<i64> = Vec::new();
    i = 0;
    while i <= n_us {
        dp.push(0);
        i += 1;
    }
    dp[n_us] = 1;

    let modv: i64 = 1000000007;
    let mut idx = 0usize;

    while idx < order.len() {
        let key = order[idx];
        let u = (key % base) as usize;

        if u != n_us {
            let row = &adj[u];
            let mut j = 0usize;
            let mut sum: i64 = 0;

            while j < row.len() {
                let v = row[j] as usize;
                if dist[v] < dist[u] {
                    sum = (sum + dp[v]) % modv;
                }
                j += 2;
            }

            dp[u] = sum;
        }

        idx += 1;
    }

    dp[1] % modv
}
