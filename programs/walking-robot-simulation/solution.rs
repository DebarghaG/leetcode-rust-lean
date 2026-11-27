pub fn robot_sim(commands: &[i64], obstacles: &[Vec<i64>]) -> i64 {
    let offset: i64 = 1_000_000;
    let base: i64 = 10_000_000;

    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < obstacles.len() {
        let ox = obstacles[i][0];
        let oy = obstacles[i][1];
        let key = (ox + offset) * base + (oy + offset);
        keys.push(key);
        i += 1;
    }

    if keys.len() > 1 {
        keys.sort();
    }

    let mut x: i64 = 0;
    let mut y: i64 = 0;
    let mut dir: i64 = 0; // 0 north, 1 east, 2 south, 3 west
    let mut max_dist: i64 = 0;

    let mut ci: usize = 0;
    while ci < commands.len() {
        let cmd = commands[ci];

        if cmd == -2 {
            dir = (dir + 3) % 4;
        } else if cmd == -1 {
            dir = (dir + 1) % 4;
        } else {
            let mut step: i64 = 0;
            while step < cmd {
                let mut nx = x;
                let mut ny = y;

                if dir == 0 {
                    ny = y + 1;
                } else if dir == 1 {
                    nx = x + 1;
                } else if dir == 2 {
                    ny = y - 1;
                } else {
                    nx = x - 1;
                }

                let candidate_key = (nx + offset) * base + (ny + offset);
                if contains(&keys, candidate_key) {
                    break;
                }

                x = nx;
                y = ny;

                let d = x * x + y * y;
                if d > max_dist {
                    max_dist = d;
                }

                step += 1;
            }
        }

        ci += 1;
    }

    max_dist
}

fn contains(keys: &[i64], target: i64) -> bool {
    let mut lo: usize = 0;
    let mut hi: usize = keys.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let value = keys[mid];

        if value == target {
            return true;
        }

        if value < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    false
}
