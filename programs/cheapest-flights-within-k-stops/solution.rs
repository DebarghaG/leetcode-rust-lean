pub fn find_cheapest_price(n: i64, flights: &[Vec<i64>], src: i64, dst: i64, k: i64) -> i64 {
    let n_us = n as usize;
    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dist: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n_us {
        dist.push(inf);
        i += 1;
    }
    dist[src as usize] = 0;

    let mut step: i64 = 0;
    while step <= k {
        let mut next: Vec<i64> = Vec::new();
        let mut i = 0;
        while i < n_us {
            next.push(dist[i]);
            i += 1;
        }

        let mut j = 0;
        while j < flights.len() {
            let flight = &flights[j];
            let from = flight[0] as usize;
            let to = flight[1] as usize;
            let price = flight[2];

            if dist[from] != inf {
                let candidate = dist[from] + price;
                if candidate < next[to] {
                    next[to] = candidate;
                }
            }

            j += 1;
        }

        dist = next;
        step += 1;
    }

    let answer = dist[dst as usize];
    if answer == inf {
        -1
    } else {
        answer
    }
}
