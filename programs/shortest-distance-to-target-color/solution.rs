pub fn shortest_distance_color(colors: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n: usize = colors.len();

    let mut dist: Vec<i64> = Vec::new();
    let total: usize = n * 3;
    let mut t: usize = 0;
    while t < total {
        dist.push(-1);
        t += 1;
    }

    let mut ci: usize = 0;
    while ci < 3 {
        let base: usize = ci * n;

        let target: i64 = if ci == 0 {
            1
        } else if ci == 1 {
            2
        } else {
            3
        };

        let mut last: i64 = -1;
        let mut i: usize = 0;
        while i < n {
            if colors[i] == target {
                last = i as i64;
            }
            if last >= 0 {
                dist[base + i] = (i as i64) - last;
            }
            i += 1;
        }

        last = -1;
        let mut j: usize = n;
        while j > 0 {
            j -= 1;
            if colors[j] == target {
                last = j as i64;
            }
            if last >= 0 {
                let d: i64 = last - (j as i64);
                let idx: usize = base + j;
                if dist[idx] < 0 || d < dist[idx] {
                    dist[idx] = d;
                }
            }
        }

        ci += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut q: usize = 0;
    while q < queries.len() {
        let query = &queries[q];
        let pos: usize = query[0] as usize;
        let color: i64 = query[1];

        if color >= 1 && color <= 3 && pos < n {
            let base: usize = ((color - 1) as usize) * n;
            ans.push(dist[base + pos]);
        } else {
            ans.push(-1);
        }

        q += 1;
    }

    ans
}
