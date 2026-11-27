pub fn shortest_alternating_paths(n: i64, redEdges: &[Vec<i64>], blueEdges: &[Vec<i64>]) -> Vec<i64> {
    let n_usize = n as usize;
    let total_states = n_usize * 2;

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total_states {
        dist.push(-1);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();

    if n_usize > 0 {
        // State encoding: node * 2 + color
        // color 0 means the last used edge was red.
        // color 1 means the last used edge was blue.
        dist[0] = 0;
        dist[1] = 0;
        queue.push(0);
        queue.push(1);
    }

    let mut head: usize = 0;
    while head < queue.len() {
        let state = queue[head];
        head += 1;

        let node = state / 2;
        let color = state % 2;
        let d = dist[state as usize];

        if color == 0 {
            // Last edge was red, so only blue edges may be used next.
            let mut j: usize = 0;
            while j < blueEdges.len() {
                let a = blueEdges[j][0];
                let b = blueEdges[j][1];

                if a == node {
                    let next_state = b * 2 + 1;
                    let next_idx = next_state as usize;

                    if dist[next_idx] == -1 {
                        dist[next_idx] = d + 1;
                        queue.push(next_state);
                    }
                }

                j += 1;
            }
        } else {
            // Last edge was blue, so only red edges may be used next.
            let mut j: usize = 0;
            while j < redEdges.len() {
                let a = redEdges[j][0];
                let b = redEdges[j][1];

                if a == node {
                    let next_state = b * 2;
                    let next_idx = next_state as usize;

                    if dist[next_idx] == -1 {
                        dist[next_idx] = d + 1;
                        queue.push(next_state);
                    }
                }

                j += 1;
            }
        }
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut v: usize = 0;

    while v < n_usize {
        let d_red = dist[2 * v];
        let d_blue = dist[2 * v + 1];

        let mut best: i64 = -1;

        if d_red != -1 && d_blue != -1 {
            if d_red < d_blue {
                best = d_red;
            } else {
                best = d_blue;
            }
        } else if d_red != -1 {
            best = d_red;
        } else if d_blue != -1 {
            best = d_blue;
        }

        answer.push(best);
        v += 1;
    }

    answer
}
