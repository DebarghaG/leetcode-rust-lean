pub fn has_path(maze: &[Vec<i64>], start: &[i64], destination: &[i64]) -> bool {
    if maze.len() == 0 || maze[0].len() == 0 {
        return false;
    }

    let m = maze.len();
    let n = maze[0].len();
    let m_i = m as i64;
    let n_i = n as i64;

    let start_r = start[0];
    let start_c = start[1];
    let dest_r = destination[0];
    let dest_c = destination[1];

    let mut found = false;

    if start_r == dest_r && start_c == dest_c {
        found = true;
    }

    if !found {
        let mut visited: Vec<Vec<bool>> = Vec::new();
        let mut i = 0;
        while i < m {
            let mut row: Vec<bool> = Vec::new();
            let mut j = 0;
            while j < n {
                row.push(false);
                j += 1;
            }
            visited.push(row);
            i += 1;
        }

        visited[start_r as usize][start_c as usize] = true;

        let mut stack_r: Vec<i64> = Vec::new();
        let mut stack_c: Vec<i64> = Vec::new();
        stack_r.push(start_r);
        stack_c.push(start_c);

        while stack_r.len() > 0 && !found {
            let idx = stack_r.len() - 1;
            let r = stack_r[idx];
            let c = stack_c[idx];
            stack_r.pop();
            stack_c.pop();

            let mut d: i64 = 0;
            while d < 4 && !found {
                let mut dr: i64 = 0;
                let mut dc: i64 = 0;

                if d == 0 {
                    dr = -1;
                } else if d == 1 {
                    dr = 1;
                } else if d == 2 {
                    dc = -1;
                } else {
                    dc = 1;
                }

                let mut pr = r;
                let mut pc = c;
                let mut nr = pr + dr;
                let mut nc = pc + dc;

                while nr >= 0
                    && nr < m_i
                    && nc >= 0
                    && nc < n_i
                    && maze[nr as usize][nc as usize] == 0
                {
                    pr = nr;
                    pc = nc;
                    nr = pr + dr;
                    nc = pc + dc;
                }

                if pr == dest_r && pc == dest_c {
                    found = true;
                } else {
                    let pr_u = pr as usize;
                    let pc_u = pc as usize;

                    if !visited[pr_u][pc_u] {
                        visited[pr_u][pc_u] = true;
                        stack_r.push(pr);
                        stack_c.push(pc);
                    }
                }

                d += 1;
            }
        }
    }

    found
}
