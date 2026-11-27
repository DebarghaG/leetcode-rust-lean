pub fn can_visit_all_rooms(rooms: &[Vec<i64>]) -> bool {
    let n = rooms.len();
    if n == 0 {
        return true;
    }

    let mut visited: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        visited.push(false);
        i += 1;
    }

    visited[0] = true;
    let mut count: usize = 1;

    let mut queue: Vec<i64> = Vec::new();
    queue.push(0);
    let mut head: usize = 0;

    while head < queue.len() {
        let cur_i64 = queue[head];
        head += 1;

        let cur = cur_i64 as usize;
        let row = &rooms[cur];

        let mut j: usize = 0;
        while j < row.len() {
            let key_i64 = row[j];
            let key = key_i64 as usize;

            if !visited[key] {
                visited[key] = true;
                count += 1;
                queue.push(key_i64);
            }

            j += 1;
        }
    }

    count == n
}
