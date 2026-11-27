fn encode(x: i64, y: i64) -> i64 {
    x * 1000000 + y
}

fn set_contains(table: &Vec<i64>, key: i64) -> bool {
    let cap = table.len();
    let mut found = false;
    if cap != 0 {
        let cap_i = cap as i64;
        let mut h = key % cap_i;
        let mut idx = h as usize;

        let mut steps: usize = 0;
        let mut done = false;
        while steps < cap && !done {
            let v = table[idx];
            if v == -1 {
                done = true;
            } else if v == key {
                found = true;
                done = true;
            } else {
                idx += 1;
                if idx == cap {
                    idx = 0;
                }
                steps += 1;
            }
        }
    }
    found
}

fn set_add(table: &mut Vec<i64>, key: i64) -> bool {
    let cap = table.len();
    let mut added = false;
    if cap != 0 {
        let cap_i = cap as i64;
        let mut h = key % cap_i;
        let mut idx = h as usize;

        let mut steps: usize = 0;
        let mut done = false;
        while steps < cap && !done {
            let v = table[idx];
            if v == -1 {
                table[idx] = key;
                added = true;
                done = true;
            } else if v == key {
                done = true;
            } else {
                idx += 1;
                if idx == cap {
                    idx = 0;
                }
                steps += 1;
            }
        }
    }
    added
}

fn bfs(
    blocked_set: &Vec<i64>,
    sx: i64,
    sy: i64,
    tx: i64,
    ty: i64,
    limit: i64,
) -> bool {
    let mut result = false;
    if sx == tx && sy == ty {
        result = true;
    } else {
        let mut cap: usize = 16;
        let need: usize = (limit as usize + 2) * 4 + 16;
        while cap < need {
            cap = cap * 2;
        }

        let mut visited: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < cap {
            visited.push(-1);
            i += 1;
        }

        let mut qx: Vec<i64> = Vec::new();
        let mut qy: Vec<i64> = Vec::new();

        qx.push(sx);
        qy.push(sy);
        set_add(&mut visited, encode(sx, sy));

        let mut count: i64 = 1;
        let mut head: usize = 0;
        let mut escaped = false;
        let mut found = false;

        while head < qx.len() && !escaped && !found {
            let x = qx[head];
            let y = qy[head];
            head += 1;

            let mut dir: i64 = 0;
            while dir < 4 && !escaped && !found {
                let mut nx = x;
                let mut ny = y;

                if dir == 0 {
                    nx = x + 1;
                } else if dir == 1 {
                    nx = x - 1;
                } else if dir == 2 {
                    ny = y + 1;
                } else {
                    ny = y - 1;
                }

                if nx >= 0 && nx < 1000000 && ny >= 0 && ny < 1000000 {
                    let key = encode(nx, ny);

                    if !set_contains(blocked_set, key) {
                        if nx == tx && ny == ty {
                            found = true;
                        } else if set_add(&mut visited, key) {
                            count += 1;
                            if count > limit {
                                escaped = true;
                            } else {
                                qx.push(nx);
                                qy.push(ny);
                            }
                        }
                    }
                }

                dir += 1;
            }
        }

        if found || escaped {
            result = true;
        }
    }
    result
}

pub fn is_escape_possible(blocked: &[Vec<i64>], source: &[i64], target: &[i64]) -> bool {
    let mut result = true;

    if blocked.len() != 0 {
        let mut blocked_set: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < 1024 {
            blocked_set.push(-1);
            i += 1;
        }

        let mut unique_blocked: i64 = 0;
        i = 0;
        while i < blocked.len() {
            let key = encode(blocked[i][0], blocked[i][1]);
            if set_add(&mut blocked_set, key) {
                unique_blocked += 1;
            }
            i += 1;
        }

        if unique_blocked != 0 {
            let limit = unique_blocked * unique_blocked;

            let sx = source[0];
            let sy = source[1];
            let tx = target[0];
            let ty = target[1];

            let mut ok = bfs(&blocked_set, sx, sy, tx, ty, limit);
            if ok {
                ok = bfs(&blocked_set, tx, ty, sx, sy, limit);
            }
            result = ok;
        }
    }

    result
}
