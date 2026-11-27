pub fn minimum_cost(n: i64, highways: &[Vec<i64>], discounts: i64) -> i64 {
    let n_usize = n as usize;

    let mut max_disc = discounts;
    let n_minus_one = n - 1;
    if max_disc > n_minus_one {
        max_disc = n_minus_one;
    }
    if max_disc < 0 {
        max_disc = 0;
    }

    let d_usize = max_disc as usize;
    let layers = d_usize + 1;

    let mut head: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n_usize {
        head.push(-1);
        i += 1;
    }

    let mut to: Vec<i64> = Vec::new();
    let mut cost: Vec<i64> = Vec::new();
    let mut next_edge: Vec<i64> = Vec::new();

    i = 0;
    while i < highways.len() {
        let h = &highways[i];
        let a = h[0] as usize;
        let b = h[1] as usize;
        let c = h[2];

        let e1 = to.len() as i64;
        to.push(b as i64);
        cost.push(c);
        next_edge.push(head[a]);
        head[a] = e1;

        let e2 = to.len() as i64;
        to.push(a as i64);
        cost.push(c);
        next_edge.push(head[b]);
        head[b] = e2;

        i += 1;
    }

    let total = n_usize * layers;
    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dist: Vec<i64> = Vec::new();
    i = 0;
    while i < total {
        dist.push(inf);
        i += 1;
    }
    dist[0] = 0;

    let mut heap_keys: Vec<i64> = Vec::new();
    let mut heap_vals: Vec<i64> = Vec::new();
    let mut heap_len: usize = 0;

    heap_keys.push(0);
    heap_vals.push(0);
    heap_len = 1;

    let target = n_usize - 1;
    let mut ans: i64 = -1;

    while heap_len > 0 {
        let cur_dist = heap_keys[0];
        let cur_state_i64 = heap_vals[0];

        if heap_len == 1 {
            heap_len = 0;
        } else {
            heap_len = heap_len - 1;
            heap_keys[0] = heap_keys[heap_len];
            heap_vals[0] = heap_vals[heap_len];

            let len = heap_len;
            let mut hi = 0;
            while hi < len {
                let l = 2 * hi + 1;
                if l >= len {
                    break;
                }

                let mut smallest = l;
                let r = l + 1;
                if r < len {
                    if heap_keys[r] < heap_keys[l] {
                        smallest = r;
                    }
                }

                if heap_keys[hi] <= heap_keys[smallest] {
                    break;
                }

                let tk = heap_keys[hi];
                heap_keys[hi] = heap_keys[smallest];
                heap_keys[smallest] = tk;

                let tv = heap_vals[hi];
                heap_vals[hi] = heap_vals[smallest];
                heap_vals[smallest] = tv;

                hi = smallest;
            }
        }

        let cur_state = cur_state_i64 as usize;
        if cur_state >= total {
            continue;
        }
        if cur_dist != dist[cur_state] {
            continue;
        }

        let city = cur_state / layers;
        let used = cur_state % layers;

        if city == target {
            ans = cur_dist;
            break;
        }

        let mut e = head[city];
        while e != -1 {
            let ei = e as usize;
            let v = to[ei] as usize;
            let toll = cost[ei];

            let nid = v * layers + used;
            let nd = cur_dist + toll;
            if nd < dist[nid] {
                dist[nid] = nd;

                if heap_len == heap_keys.len() {
                    heap_keys.push(nd);
                    heap_vals.push(nid as i64);
                } else {
                    heap_keys[heap_len] = nd;
                    heap_vals[heap_len] = nid as i64;
                }

                let mut hi = heap_len;
                heap_len = heap_len + 1;

                while hi > 0 {
                    let p = (hi - 1) / 2;
                    if heap_keys[p] <= heap_keys[hi] {
                        break;
                    }

                    let tk = heap_keys[p];
                    heap_keys[p] = heap_keys[hi];
                    heap_keys[hi] = tk;

                    let tv = heap_vals[p];
                    heap_vals[p] = heap_vals[hi];
                    heap_vals[hi] = tv;

                    hi = p;
                }
            }

            if used < d_usize {
                let nid2 = v * layers + used + 1;
                let nd2 = cur_dist + toll / 2;

                if nd2 < dist[nid2] {
                    dist[nid2] = nd2;

                    if heap_len == heap_keys.len() {
                        heap_keys.push(nd2);
                        heap_vals.push(nid2 as i64);
                    } else {
                        heap_keys[heap_len] = nd2;
                        heap_vals[heap_len] = nid2 as i64;
                    }

                    let mut hi = heap_len;
                    heap_len = heap_len + 1;

                    while hi > 0 {
                        let p = (hi - 1) / 2;
                        if heap_keys[p] <= heap_keys[hi] {
                            break;
                        }

                        let tk = heap_keys[p];
                        heap_keys[p] = heap_keys[hi];
                        heap_keys[hi] = tk;

                        let tv = heap_vals[p];
                        heap_vals[p] = heap_vals[hi];
                        heap_vals[hi] = tv;

                        hi = p;
                    }
                }
            }

            e = next_edge[ei];
        }
    }

    ans
}
