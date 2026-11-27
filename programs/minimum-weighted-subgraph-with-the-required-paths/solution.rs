fn dijkstra(
    n: i64,
    head: &[i64],
    to: &[i64],
    wt: &[i64],
    next: &[i64],
    source: i64,
) -> Vec<i64> {
    let inf: i64 = 1_000_000_000_000_000_000;
    let n_usize = n as usize;

    let mut dist: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n {
        dist.push(inf);
        i += 1;
    }

    if source < 0 || source >= n {
        return dist;
    }

    let su = source as usize;
    dist[su] = 0;

    let base = n + 1;

    let mut heap: Vec<i64> = Vec::new();
    heap.push(source);
    let mut heap_len: usize = 1;

    while heap_len > 0 {
        let key = heap[0];
        let old_len = heap_len;
        let last = heap[old_len - 1];
        heap_len = old_len - 1;

        if heap_len > 0 {
            heap[0] = last;

            let mut idx: usize = 0;
            let mut stop = false;
            while !stop && idx < heap_len {
                let left = 2 * idx + 1;
                if left >= heap_len {
                    stop = true;
                } else {
                    let right = left + 1;
                    let mut smallest = left;
                    if right < heap_len && heap[right] < heap[left] {
                        smallest = right;
                    }

                    if heap[idx] <= heap[smallest] {
                        stop = true;
                    } else {
                        let tmp = heap[idx];
                        heap[idx] = heap[smallest];
                        heap[smallest] = tmp;
                        idx = smallest;
                    }
                }
            }
        }

        let d = key / base;
        let u = key % base;

        if u < n {
            let ui = u as usize;

            if d == dist[ui] {
                let mut e = head[ui];
                while e != -1 {
                    let ei = e as usize;
                    let v = to[ei];
                    let nd = d + wt[ei];
                    let vi = v as usize;

                    if nd < dist[vi] {
                        dist[vi] = nd;

                        let new_key = nd * base + v;
                        if heap_len < heap.len() {
                            heap[heap_len] = new_key;
                        } else {
                            heap.push(new_key);
                        }
                        heap_len += 1;

                        let mut idx = heap_len - 1;
                        let mut stop2 = false;
                        while !stop2 && idx > 0 {
                            let p = (idx - 1) / 2;
                            if heap[p] <= heap[idx] {
                                stop2 = true;
                            } else {
                                let tmp = heap[p];
                                heap[p] = heap[idx];
                                heap[idx] = tmp;
                                idx = p;
                            }
                        }
                    }

                    e = next[ei];
                }
            }
        }
    }

    dist
}

pub fn minimum_weight(
    n: i64,
    edges: &[Vec<i64>],
    src1: i64,
    src2: i64,
    dest: i64,
) -> i64 {
    let inf: i64 = 1_000_000_000_000_000_000;
    let n_usize = n as usize;

    let mut head_f: Vec<i64> = Vec::new();
    let mut head_r: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n_usize {
        head_f.push(-1);
        head_r.push(-1);
        i += 1;
    }

    let mut to_f: Vec<i64> = Vec::new();
    let mut wt_f: Vec<i64> = Vec::new();
    let mut next_f: Vec<i64> = Vec::new();

    let mut to_r: Vec<i64> = Vec::new();
    let mut wt_r: Vec<i64> = Vec::new();
    let mut next_r: Vec<i64> = Vec::new();

    let mut e: usize = 0;
    while e < edges.len() {
        let u = edges[e][0];
        let v = edges[e][1];
        let w = edges[e][2];

        let ui = u as usize;
        let vi = v as usize;

        to_f.push(v);
        wt_f.push(w);
        next_f.push(head_f[ui]);
        head_f[ui] = e as i64;

        to_r.push(u);
        wt_r.push(w);
        next_r.push(head_r[vi]);
        head_r[vi] = e as i64;

        e += 1;
    }

    let d1 = dijkstra(n, &head_f, &to_f, &wt_f, &next_f, src1);
    let d2 = dijkstra(n, &head_f, &to_f, &wt_f, &next_f, src2);
    let d3 = dijkstra(n, &head_r, &to_r, &wt_r, &next_r, dest);

    let mut ans = inf;
    let mut node: usize = 0;

    while node < n_usize {
        if d1[node] != inf && d2[node] != inf && d3[node] != inf {
            let sum = d1[node] + d2[node] + d3[node];
            if sum < ans {
                ans = sum;
            }
        }
        node += 1;
    }

    if ans == inf {
        -1
    } else {
        ans
    }
}
