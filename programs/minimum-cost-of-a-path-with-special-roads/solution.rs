fn manhattan(x1: i64, y1: i64, x2: i64, y2: i64) -> i64 {
    let dx = if x1 >= x2 { x1 - x2 } else { x2 - x1 };
    let dy = if y1 >= y2 { y1 - y2 } else { y2 - y1 };
    dx + dy
}

pub fn minimum_cost(start: &[i64], target: &[i64], specialRoads: &[Vec<i64>]) -> i64 {
    let sx = start[0];
    let sy = start[1];
    let tx = target[0];
    let ty = target[1];

    let n = specialRoads.len();
    let inf: i64 = 1000000000000000000;

    let mut ans = manhattan(sx, sy, tx, ty);

    let mut dist: Vec<i64> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let d = manhattan(sx, sy, specialRoads[i][0], specialRoads[i][1]);
        dist.push(d);
        visited.push(false);
        i += 1;
    }

    let mut done: usize = 0;
    while done < n {
        let mut u: usize = n;
        let mut best: i64 = inf;

        let mut j: usize = 0;
        while j < n {
            if !visited[j] {
                if dist[j] < best {
                    best = dist[j];
                    u = j;
                }
            }
            j += 1;
        }

        if u == n {
            break;
        }

        visited[u] = true;

        let ux = specialRoads[u][0];
        let uy = specialRoads[u][1];
        let ex = specialRoads[u][2];
        let ey = specialRoads[u][3];
        let road_cost = specialRoads[u][4];

        let after_road = dist[u] + road_cost;

        let via_target = after_road + manhattan(ex, ey, tx, ty);
        if via_target < ans {
            ans = via_target;
        }

        let via_walk = dist[u] + manhattan(ux, uy, tx, ty);
        if via_walk < ans {
            ans = via_walk;
        }

        let mut v: usize = 0;
        while v < n {
            if !visited[v] {
                let cand = after_road
                    + manhattan(ex, ey, specialRoads[v][0], specialRoads[v][1]);
                if cand < dist[v] {
                    dist[v] = cand;
                }
            }
            v += 1;
        }

        done += 1;
    }

    ans
}
