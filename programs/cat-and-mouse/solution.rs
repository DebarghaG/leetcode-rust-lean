pub fn cat_mouse_game(graph: &[Vec<i64>]) -> i64 {
    let n = graph.len();
    let total = n * n * 2;

    let mut res: Vec<i64> = Vec::new();
    let mut degree: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < total {
        res.push(0);
        degree.push(0);
        z += 1;
    }

    let mut queue: Vec<i64> = Vec::new();

    // Initialize terminal states and out-degrees.
    let mut mouse = 0;
    while mouse < n {
        let mut cat = 1;
        while cat < n {
            let id0 = (mouse * n + cat) * 2;
            let id1 = id0 + 1;

            // Mouse to move: all outgoing edges are valid.
            degree[id0] = graph[mouse].len() as i64;

            // Cat to move: cat may not move to node 0.
            let mut cnt: i64 = 0;
            let rowc = &graph[cat];
            let mut j = 0;
            while j < rowc.len() {
                if rowc[j] != 0 {
                    cnt += 1;
                }
                j += 1;
            }
            degree[id1] = cnt;

            if mouse == 0 {
                // Mouse has reached the hole.
                res[id0] = 1;
                res[id1] = 1;
                queue.push(id0 as i64);
                queue.push(id1 as i64);
            } else if mouse == cat {
                // Cat has caught the mouse.
                res[id0] = 2;
                res[id1] = 2;
                queue.push(id0 as i64);
                queue.push(id1 as i64);
            }

            cat += 1;
        }
        mouse += 1;
    }

    // Retrograde analysis.
    let mut head = 0;
    while head < queue.len() {
        let sid = queue[head] as usize;
        head += 1;

        let r = res[sid];
        let turn = sid % 2;
        let tmp = sid / 2;
        let cat = tmp % n;
        let mouse = tmp / n;

        if turn == 0 {
            // Current state: mouse to move.
            // Predecessors: cat to move, cat moved from pc to cat.
            let list = &graph[cat];
            let mut k = 0;
            while k < list.len() {
                let pc = list[k] as usize;
                if pc != 0 {
                    let pid = (mouse * n + pc) * 2 + 1;
                    if res[pid] == 0 {
                        if r == 2 {
                            res[pid] = 2;
                            queue.push(pid as i64);
                        } else {
                            degree[pid] -= 1;
                            if degree[pid] == 0 {
                                res[pid] = 1;
                                queue.push(pid as i64);
                            }
                        }
                    }
                }
                k += 1;
            }
        } else {
            // Current state: cat to move.
            // Predecessors: mouse to move, mouse moved from pm to mouse.
            let list = &graph[mouse];
            let mut k = 0;
            while k < list.len() {
                let pm = list[k] as usize;
                let pid = (pm * n + cat) * 2;
                if res[pid] == 0 {
                    if r == 1 {
                        res[pid] = 1;
                        queue.push(pid as i64);
                    } else {
                        degree[pid] -= 1;
                        if degree[pid] == 0 {
                            res[pid] = 2;
                            queue.push(pid as i64);
                        }
                    }
                }
                k += 1;
            }
        }
    }

    // Initial state: mouse at 1, cat at 2, mouse to move.
    let start = (1 * n + 2) * 2;
    res[start]
}
