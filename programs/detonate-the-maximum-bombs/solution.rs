pub fn maximum_detonation(bombs: &[Vec<i64>]) -> i64 {
    let n: usize = bombs.len();
    if n == 0 {
        return 0;
    }

    let mut best: i64 = 0;
    let mut start: usize = 0;

    while start < n {
        let mut visited: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            visited.push(false);
            k += 1;
        }

        let mut queue: Vec<usize> = Vec::new();
        queue.push(start);
        visited[start] = true;

        let mut count: i64 = 1;
        let mut head: usize = 0;

        while head < queue.len() {
            let i: usize = queue[head];
            head += 1;

            let xi: i64 = bombs[i][0];
            let yi: i64 = bombs[i][1];
            let ri: i64 = bombs[i][2];
            let r2: i64 = ri * ri;

            let mut j: usize = 0;
            while j < n {
                if !visited[j] {
                    let xj: i64 = bombs[j][0];
                    let yj: i64 = bombs[j][1];
                    let dx: i64 = xi - xj;
                    let dy: i64 = yi - yj;
                    let dist2: i64 = dx * dx + dy * dy;

                    if dist2 <= r2 {
                        visited[j] = true;
                        queue.push(j);
                        count += 1;
                    }
                }
                j += 1;
            }
        }

        if count > best {
            best = count;
        }

        start += 1;
    }

    best
}
