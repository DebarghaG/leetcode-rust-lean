pub fn possible_bipartition(n: i64, dislikes: &[Vec<i64>]) -> bool {
    let m = n as usize + 1;

    // color[v] = -1 (unvisited), 0 or 1 (the two groups)
    let mut color: Vec<i64> = Vec::new();
    let mut ci: usize = 0;
    while ci < m {
        color.push(-1);
        ci += 1;
    }

    let mut ok: bool = true;
    let mut start: usize = 1;

    while start < m && ok {
        if color[start] == -1 {
            color[start] = 0;

            // BFS from this component seed.
            let mut queue: Vec<i64> = Vec::new();
            queue.push(start as i64);
            let mut head: usize = 0;

            while head < queue.len() && ok {
                let u = queue[head];
                head += 1;
                let cu = color[u as usize];

                let mut e: usize = 0;
                while e < dislikes.len() && ok {
                    let a = dislikes[e][0];
                    let b = dislikes[e][1];

                    if a == u {
                        if color[b as usize] == -1 {
                            color[b as usize] = 1 - cu;
                            queue.push(b);
                        } else if color[b as usize] == cu {
                            ok = false;
                        }
                    } else if b == u {
                        if color[a as usize] == -1 {
                            color[a as usize] = 1 - cu;
                            queue.push(a);
                        } else if color[a as usize] == cu {
                            ok = false;
                        }
                    }

                    e += 1;
                }
            }
        }

        start += 1;
    }

    ok
}
