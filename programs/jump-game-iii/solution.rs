pub fn can_reach(arr: &[i64], start: i64) -> bool {
    let n: usize = arr.len();
    if n == 0 {
        return false;
    }

    let n_i64: i64 = n as i64;
    let start_idx: usize = start as usize;
    if start_idx >= n {
        return false;
    }

    let mut visited: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        visited.push(0);
        i = i + 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    queue.push(start);
    visited[start_idx] = 1;

    let mut head: usize = 0;
    while head < queue.len() {
        let idx_i64: i64 = queue[head];
        head = head + 1;
        let idx: usize = idx_i64 as usize;

        if arr[idx] == 0 {
            return true;
        }

        let step: i64 = arr[idx];

        let plus: i64 = idx_i64 + step;
        if plus >= 0 && plus < n_i64 {
            let j: usize = plus as usize;
            if visited[j] == 0 {
                visited[j] = 1;
                queue.push(plus);
            }
        }

        let minus: i64 = idx_i64 - step;
        if minus >= 0 && minus < n_i64 {
            let j: usize = minus as usize;
            if visited[j] == 0 {
                visited[j] = 1;
                queue.push(minus);
            }
        }
    }

    false
}
