pub fn min_cost(n: i64, roads: &[Vec<i64>], appleCost: &[i64], k: i64) -> Vec<i64> {
    let nn: usize = n as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let mut r: usize = 0;
    while r < roads.len() {
        let a: usize = (roads[r][0] - 1) as usize;
        let b: usize = (roads[r][1] - 1) as usize;
        let c: i64 = roads[r][2];

        adj[a].push(b as i64);
        adj[a].push(c);
        adj[b].push(a as i64);
        adj[b].push(c);

        r += 1;
    }

    let mult: i64 = k + 1;

    let mut dist: Vec<i64> = Vec::new();
    i = 0;
    while i < nn {
        dist.push(appleCost[i]);
        i += 1;
    }

    let mut visited: Vec<bool> = Vec::new();
    i = 0;
    while i < nn {
        visited.push(false);
        i += 1;
    }

    let mut step: usize = 0;
    while step < nn {
        let mut best_idx: usize = nn;
        let mut best_val: i64 = 0;
        let mut found: bool = false;

        let mut j: usize = 0;
        while j < nn {
            if !visited[j] && (!found || dist[j] < best_val) {
                best_val = dist[j];
                best_idx = j;
                found = true;
            }
            j += 1;
        }

        if found {
            visited[best_idx] = true;

            let base: i64 = dist[best_idx];
            let row = &adj[best_idx];

            let mut e: usize = 0;
            while e < row.len() {
                let v: usize = row[e] as usize;
                let w: i64 = row[e + 1];
                let cand: i64 = base + w * mult;

                if cand < dist[v] {
                    dist[v] = cand;
                }

                e += 2;
            }

            step += 1;
        } else {
            step = nn;
        }
    }

    dist
}
