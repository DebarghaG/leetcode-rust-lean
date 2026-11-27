pub fn find_the_city(n: i64, edges: &[Vec<i64>], distanceThreshold: i64) -> i64 {
    let n_usize = n as usize;
    let inf: i64 = 1_000_000_000;

    let mut dist: Vec<Vec<i64>> = Vec::new();

    let mut i: usize = 0;
    while i < n_usize {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n_usize {
            if i == j {
                row.push(0);
            } else {
                row.push(inf);
            }
            j += 1;
        }
        dist.push(row);
        i += 1;
    }

    let mut e: usize = 0;
    while e < edges.len() {
        let u = edges[e][0] as usize;
        let v = edges[e][1] as usize;
        let w = edges[e][2];

        if w < dist[u][v] {
            dist[u][v] = w;
            dist[v][u] = w;
        }

        e += 1;
    }

    let mut k: usize = 0;
    while k < n_usize {
        let mut i: usize = 0;
        while i < n_usize {
            let mut j: usize = 0;
            while j < n_usize {
                let via = dist[i][k] + dist[k][j];
                if via < dist[i][j] {
                    dist[i][j] = via;
                }
                j += 1;
            }
            i += 1;
        }
        k += 1;
    }

    let mut best_city: i64 = 0;
    let mut best_count: i64 = n + 1;

    let mut city: usize = 0;
    while city < n_usize {
        let mut count: i64 = 0;
        let mut other: usize = 0;

        while other < n_usize {
            if other != city && dist[city][other] <= distanceThreshold {
                count += 1;
            }
            other += 1;
        }

        if count <= best_count {
            best_count = count;
            best_city = city as i64;
        }

        city += 1;
    }

    best_city
}
