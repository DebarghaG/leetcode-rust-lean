const INF: i64 = 1_000_000_000_000_000_000;

fn heap_push(heap: &mut Vec<i64>, x: i64) {
    let mut i: usize = heap.len();
    heap.push(x);

    while i > 0 {
        let p = (i - 1) / 2;
        if heap[p] <= heap[i] {
            break;
        }
        let tmp = heap[p];
        heap[p] = heap[i];
        heap[i] = tmp;
        i = p;
    }
}

fn heap_pop(heap: &mut Vec<i64>) -> i64 {
    let n = heap.len();
    let top = heap[0];
    let last = heap[n - 1];
    heap.pop();

    if n > 1 {
        heap[0] = last;
        let len = n - 1;
        let mut i: usize = 0;

        loop {
            let l = 2 * i + 1;
            if l >= len {
                break;
            }

            let r = l + 1;
            let mut s = l;
            if r < len && heap[r] < heap[l] {
                s = r;
            }

            if heap[i] <= heap[s] {
                break;
            }

            let tmp = heap[i];
            heap[i] = heap[s];
            heap[s] = tmp;
            i = s;
        }
    }

    top
}

fn dijkstra(n: i64, adj: &[Vec<i64>], src: i64) -> Vec<i64> {
    let n_usize = n as usize;
    let mut dist: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n_usize {
        dist.push(INF);
        i += 1;
    }

    let s = src as usize;
    dist[s] = 0;

    let base = n + 1;
    let mut heap: Vec<i64> = Vec::new();
    heap_push(&mut heap, src);

    while !heap.is_empty() {
        let code = heap_pop(&mut heap);
        let du = code / base;
        let u = (code % base) as usize;

        if du != dist[u] {
            continue;
        }

        let row = &adj[u];
        let mut j: usize = 0;
        while j < row.len() {
            let v = row[j] as usize;
            let w = row[j + 1];
            let nd = du + w;

            if nd < dist[v] {
                dist[v] = nd;
                let new_code = nd * base + (v as i64);
                heap_push(&mut heap, new_code);
            }

            j += 2;
        }
    }

    dist
}

pub fn find_answer(n: i64, edges: &[Vec<i64>]) -> Vec<bool> {
    let n_usize = n as usize;
    let m = edges.len();

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize {
        adj.push(Vec::new());
        i += 1;
    }

    let mut e: usize = 0;
    while e < m {
        let a = edges[e][0] as usize;
        let b = edges[e][1] as usize;
        let w = edges[e][2];

        adj[a].push(b as i64);
        adj[a].push(w);

        adj[b].push(a as i64);
        adj[b].push(w);

        e += 1;
    }

    let dist0 = dijkstra(n, &adj, 0);
    let target = n - 1;
    let distt = dijkstra(n, &adj, target);

    let target_usize = target as usize;
    let shortest = dist0[target_usize];

    let mut ans: Vec<bool> = Vec::new();
    let mut k: usize = 0;

    while k < m {
        let u = edges[k][0];
        let v = edges[k][1];
        let w = edges[k][2];

        let uu = u as usize;
        let vv = v as usize;

        let mut ok = false;

        if shortest != INF {
            if dist0[uu] != INF && distt[vv] != INF {
                if dist0[uu] + w + distt[vv] == shortest {
                    ok = true;
                }
            }

            if !ok && dist0[vv] != INF && distt[uu] != INF {
                if dist0[vv] + w + distt[uu] == shortest {
                    ok = true;
                }
            }
        }

        ans.push(ok);
        k += 1;
    }

    ans
}
