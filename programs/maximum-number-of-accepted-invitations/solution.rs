pub fn maximum_invitations(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();

    // match_girl[j] = boy matched to girl j, or m if unmatched.
    let mut match_girl: Vec<usize> = Vec::new();
    let mut j = 0;
    while j < n {
        match_girl.push(m);
        j += 1;
    }

    // match_boy[i] = girl matched to boy i, or n if unmatched.
    let mut match_boy: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < m {
        match_boy.push(n);
        i += 1;
    }

    let mut result: i64 = 0;
    let mut start = 0;

    while start < m {
        let mut visited: Vec<bool> = Vec::new();
        let mut j = 0;
        while j < n {
            visited.push(false);
            j += 1;
        }

        // parent_girl[j] = boy from which girl j was reached.
        let mut parent_girl: Vec<usize> = Vec::new();
        let mut j = 0;
        while j < n {
            parent_girl.push(m);
            j += 1;
        }

        let mut queue: Vec<usize> = Vec::new();
        queue.push(start);

        let mut head = 0;
        let mut found_girl = n;

        while head < queue.len() && found_girl == n {
            let b = queue[head];
            head += 1;

            let row = &grid[b];
            let mut g = 0;
            while g < n {
                if row[g] == 1 && !visited[g] {
                    visited[g] = true;
                    parent_girl[g] = b;

                    let mb = match_girl[g];
                    if mb == m {
                        found_girl = g;
                        g = n;
                    } else {
                        queue.push(mb);
                        g += 1;
                    }
                } else {
                    g += 1;
                }
            }
        }

        if found_girl != n {
            result += 1;

            let mut g = found_girl;
            while g != n {
                let b = parent_girl[g];
                let old_girl = match_boy[b];

                match_boy[b] = g;
                match_girl[g] = b;

                g = old_girl;
            }
        }

        start += 1;
    }

    result
}
