pub fn network_delay_time(times: &[Vec<i64>], n: i64, k: i64) -> i64 {
    let nn: usize = n as usize;
    let inf: i64 = 1_000_000_000;

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nn {
        dist.push(inf);
        i += 1;
    }

    let start: usize = (k - 1) as usize;
    dist[start] = 0;

    let mut iter: usize = 0;
    while iter < nn {
        let mut e: usize = 0;
        while e < times.len() {
            let u: usize = (times[e][0] - 1) as usize;
            let v: usize = (times[e][1] - 1) as usize;
            let w: i64 = times[e][2];

            if dist[u] < inf {
                let candidate: i64 = dist[u] + w;
                if candidate < dist[v] {
                    dist[v] = candidate;
                }
            }

            e += 1;
        }
        iter += 1;
    }

    let mut ans: i64 = 0;
    let mut j: usize = 0;
    while j < nn {
        if dist[j] == inf {
            return -1;
        }
        if dist[j] > ans {
            ans = dist[j];
        }
        j += 1;
    }

    ans
}
