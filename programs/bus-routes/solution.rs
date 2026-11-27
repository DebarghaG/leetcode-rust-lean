fn find_index(xs: &[i64], x: i64) -> i64 {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if lo < xs.len() {
        if xs[lo] == x {
            return lo as i64;
        }
    }
    -1
}

fn sort_i64(v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    let mut src = v;
    let mut width: usize = 1;
    while width < n {
        let mut dst: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let mut mid = i + width;
            if mid > n {
                mid = n;
            }
            let mut end = i + width + width;
            if end > n {
                end = n;
            }
            let mut l = i;
            let mut r = mid;
            while l < mid {
                if r < end {
                    if src[l] <= src[r] {
                        dst.push(src[l]);
                        l += 1;
                    } else {
                        dst.push(src[r]);
                        r += 1;
                    }
                } else {
                    dst.push(src[l]);
                    l += 1;
                }
            }
            while r < end {
                dst.push(src[r]);
                r += 1;
            }
            i = end;
        }
        src = dst;
        width = width + width;
    }
    src
}

pub fn num_buses_to_destination(routes: &[Vec<i64>], source: i64, target: i64) -> i64 {
    if source == target {
        return 0;
    }

    let mut all_stops: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < routes.len() {
        let route = &routes[i];
        let mut j: usize = 0;
        while j < route.len() {
            all_stops.push(route[j]);
            j += 1;
        }
        i += 1;
    }

    if all_stops.len() == 0 {
        return -1;
    }

    let sorted_stops = sort_i64(all_stops);

    let mut unique: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < sorted_stops.len() {
        if k == 0 {
            unique.push(sorted_stops[k]);
        } else {
            if sorted_stops[k] != sorted_stops[k - 1] {
                unique.push(sorted_stops[k]);
            }
        }
        k += 1;
    }

    let source_idx_i = find_index(&unique, source);
    if source_idx_i < 0 {
        return -1;
    }
    let target_idx_i = find_index(&unique, target);
    if target_idx_i < 0 {
        return -1;
    }

    let m = unique.len();

    let mut counts: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < m {
        counts.push(0);
        z += 1;
    }

    let mut b: usize = 0;
    while b < routes.len() {
        let route = &routes[b];
        let mut j: usize = 0;
        while j < route.len() {
            let idx = find_index(&unique, route[j]) as usize;
            counts[idx] = counts[idx] + 1;
            j += 1;
        }
        b += 1;
    }

    let mut start: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut s: usize = 0;
    while s < m {
        start.push(sum);
        sum = sum + counts[s];
        s += 1;
    }
    start.push(sum);

    let total = sum as usize;
    let mut adj: Vec<i64> = Vec::new();
    let mut a: usize = 0;
    while a < total {
        adj.push(0);
        a += 1;
    }

    let mut pos: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < m {
        pos.push(start[p]);
        p += 1;
    }

    b = 0;
    while b < routes.len() {
        let route = &routes[b];
        let mut j: usize = 0;
        while j < route.len() {
            let idx = find_index(&unique, route[j]) as usize;
            let at = pos[idx] as usize;
            adj[at] = b as i64;
            pos[idx] = pos[idx] + 1;
            j += 1;
        }
        b += 1;
    }

    let n_buses = routes.len();

    let mut bus_visited: Vec<bool> = Vec::new();
    let mut q: usize = 0;
    while q < n_buses {
        bus_visited.push(false);
        q += 1;
    }

    let mut bus_dist: Vec<i64> = Vec::new();
    q = 0;
    while q < n_buses {
        bus_dist.push(-1);
        q += 1;
    }

    let mut stop_visited: Vec<bool> = Vec::new();
    q = 0;
    while q < m {
        stop_visited.push(false);
        q += 1;
    }

    let source_idx = source_idx_i as usize;
    stop_visited[source_idx] = true;

    let mut queue: Vec<i64> = Vec::new();

    let mut k2 = start[source_idx] as usize;
    let end2 = start[source_idx + 1] as usize;
    while k2 < end2 {
        let bus = adj[k2] as usize;
        if !bus_visited[bus] {
            bus_visited[bus] = true;
            bus_dist[bus] = 1;
            queue.push(bus as i64);
        }
        k2 += 1;
    }

    let mut answer: i64 = -1;
    let mut found: bool = false;

    let mut head: usize = 0;
    while head < queue.len() && !found {
        let bus_i = queue[head];
        head += 1;

        let bus = bus_i as usize;
        let d = bus_dist[bus];
        let route = &routes[bus];

        let mut j: usize = 0;
        while j < route.len() && !found {
            let stop_val = route[j];

            if stop_val == target {
                answer = d;
                found = true;
            } else {
                let sidx = find_index(&unique, stop_val) as usize;
                if !stop_visited[sidx] {
                    stop_visited[sidx] = true;

                    let mut e = start[sidx] as usize;
                    let end = start[sidx + 1] as usize;
                    while e < end {
                        let nb = adj[e] as usize;
                        if !bus_visited[nb] {
                            bus_visited[nb] = true;
                            bus_dist[nb] = d + 1;
                            queue.push(nb as i64);
                        }
                        e += 1;
                    }
                }
            }

            j += 1;
        }
    }

    answer
}
