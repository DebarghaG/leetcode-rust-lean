pub fn assign_bikes(workers: &[Vec<i64>], bikes: &[Vec<i64>]) -> Vec<i64> {
    let n = workers.len();
    let m = bikes.len();
    let total = n * m;

    // Find the maximum Manhattan distance.
    let mut maxd: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let wx = workers[i][0];
        let wy = workers[i][1];
        let mut j: usize = 0;
        while j < m {
            let dx = wx - bikes[j][0];
            let adx = if dx >= 0 { dx } else { -dx };
            let dy = wy - bikes[j][1];
            let ady = if dy >= 0 { dy } else { -dy };
            let d = adx + ady;
            if d > maxd {
                maxd = d;
            }
            j += 1;
        }
        i += 1;
    }

    let bucket_count = (maxd + 1) as usize;

    // Count how many pairs have each distance.
    let mut freq: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < bucket_count {
        freq.push(0);
        k += 1;
    }

    i = 0;
    while i < n {
        let wx = workers[i][0];
        let wy = workers[i][1];
        let mut j: usize = 0;
        while j < m {
            let dx = wx - bikes[j][0];
            let adx = if dx >= 0 { dx } else { -dx };
            let dy = wy - bikes[j][1];
            let ady = if dy >= 0 { dy } else { -dy };
            let d = adx + ady;
            freq[d as usize] += 1;
            j += 1;
        }
        i += 1;
    }

    // Starting index of each distance bucket.
    let mut pos: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    k = 0;
    while k < bucket_count {
        pos.push(sum);
        sum += freq[k];
        k += 1;
    }

    // Stable counting sort by distance. Within the same distance,
    // worker index and then bike index order is preserved.
    let mut ordered: Vec<i64> = Vec::new();
    k = 0;
    while k < total {
        ordered.push(0);
        k += 1;
    }

    let m_i = m as i64;
    i = 0;
    while i < n {
        let wx = workers[i][0];
        let wy = workers[i][1];
        let mut j: usize = 0;
        while j < m {
            let dx = wx - bikes[j][0];
            let adx = if dx >= 0 { dx } else { -dx };
            let dy = wy - bikes[j][1];
            let ady = if dy >= 0 { dy } else { -dy };
            let d = adx + ady;

            let code = (i as i64) * m_i + (j as i64);
            let p = pos[d as usize] as usize;
            ordered[p] = code;
            pos[d as usize] += 1;

            j += 1;
        }
        i += 1;
    }

    let mut used_w: Vec<bool> = Vec::new();
    let mut used_b: Vec<bool> = Vec::new();
    let mut ans: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        used_w.push(false);
        ans.push(-1);
        i += 1;
    }

    let mut j: usize = 0;
    while j < m {
        used_b.push(false);
        j += 1;
    }

    k = 0;
    while k < total {
        let code = ordered[k];
        let wi = code / m_i;
        let bi = code % m_i;
        let w = wi as usize;
        let b = bi as usize;

        if used_w[w] == false && used_b[b] == false {
            used_w[w] = true;
            used_b[b] = true;
            ans[w] = bi;
        }

        k += 1;
    }

    ans
}
