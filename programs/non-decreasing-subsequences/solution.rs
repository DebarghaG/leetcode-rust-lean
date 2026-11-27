pub fn find_subsequences(nums: &[i64]) -> Vec<Vec<i64>> {
    let n = nums.len();
    let n_i = n as i64;

    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut path: Vec<i64> = Vec::new();

    let mut stack_next: Vec<i64> = Vec::new();
    let mut stack_depth: Vec<i64> = Vec::new();

    let mut used: Vec<bool> = Vec::new();
    let total = (n + 1) * 201;
    let mut k: usize = 0;
    while k < total {
        used.push(false);
        k += 1;
    }

    stack_next.push(0);
    stack_depth.push(0);

    while stack_next.len() > 0 {
        let top = stack_next.len() - 1;
        let mut next_i: i64 = stack_next[top];
        let depth_i: i64 = stack_depth[top];
        let depth: usize = depth_i as usize;

        let mut found = false;
        let mut chosen_i: i64 = 0;

        while next_i < n_i {
            let i_i = next_i;
            next_i += 1;
            let i: usize = i_i as usize;

            let mut ok = true;
            if path.len() > 0 {
                if nums[i] < path[path.len() - 1] {
                    ok = false;
                }
            }

            if ok {
                let vi = (nums[i] + 100) as usize;
                if !used[depth * 201 + vi] {
                    used[depth * 201 + vi] = true;
                    chosen_i = i_i;
                    found = true;
                    break;
                }
            }
        }

        stack_next[top] = next_i;

        if found {
            let chosen: usize = chosen_i as usize;
            path.push(nums[chosen]);

            if path.len() >= 2 {
                let mut row: Vec<i64> = Vec::new();
                let mut j: usize = 0;
                while j < path.len() {
                    row.push(path[j]);
                    j += 1;
                }
                out.push(row);
            }

            let child_next = chosen_i + 1;
            let child_depth = path.len() as i64;
            stack_next.push(child_next);
            stack_depth.push(child_depth);

            let base = (child_depth as usize) * 201;
            let mut m: usize = 0;
            while m < 201 {
                used[base + m] = false;
                m += 1;
            }
        } else {
            stack_next.pop();
            stack_depth.pop();
            if depth_i > 0 {
                path.pop();
            }
        }
    }

    out
}
