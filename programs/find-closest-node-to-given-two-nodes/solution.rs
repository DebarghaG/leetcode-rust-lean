pub fn closest_meeting_node(edges: &[i64], node1: i64, node2: i64) -> i64 {
    let n = edges.len();

    let mut dist1: Vec<i64> = Vec::new();
    let mut dist2: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < n {
        dist1.push(-1);
        dist2.push(-1);
        i += 1;
    }

    let mut cur = node1;
    let mut d: i64 = 0;
    while cur != -1 {
        let idx = cur as usize;
        if dist1[idx] != -1 {
            break;
        }
        dist1[idx] = d;
        cur = edges[idx];
        d += 1;
    }

    cur = node2;
    d = 0;
    while cur != -1 {
        let idx = cur as usize;
        if dist2[idx] != -1 {
            break;
        }
        dist2[idx] = d;
        cur = edges[idx];
        d += 1;
    }

    let mut best: i64 = -1;
    let mut best_max: i64 = -1;

    i = 0;
    while i < n {
        if dist1[i] != -1 && dist2[i] != -1 {
            let mut m = dist1[i];
            if dist2[i] > m {
                m = dist2[i];
            }

            if best == -1 || m < best_max {
                best = i as i64;
                best_max = m;
            }
        }
        i += 1;
    }

    best
}
