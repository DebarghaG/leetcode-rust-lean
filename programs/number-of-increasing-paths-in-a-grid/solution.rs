pub fn count_paths(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }
    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let total = m * n;
    let modulo: i64 = 1000000007;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < total {
        dp.push(-1);
        i += 1;
    }

    let mut stack_ids: Vec<usize> = Vec::new();
    let mut stack_pos: Vec<usize> = Vec::new();
    let mut stack_acc: Vec<i64> = Vec::new();

    let mut answer: i64 = 0;
    let mut start: usize = 0;

    while start < total {
        if dp[start] == -1 {
            stack_ids.push(start);
            stack_pos.push(0);
            stack_acc.push(1);

            while stack_ids.len() > 0 {
                let top = stack_ids.len() - 1;
                let id = stack_ids[top];
                let pos = stack_pos[top];

                if pos >= 4 {
                    let value = stack_acc[top] % modulo;
                    dp[id] = value;
                    answer = (answer + value) % modulo;

                    stack_ids.pop();
                    stack_pos.pop();
                    stack_acc.pop();
                } else {
                    let r = id / n;
                    let c = id % n;
                    let cur_value = grid[r][c];

                    let mut nb_valid = false;
                    let mut nb: usize = 0;

                    if pos == 0 {
                        if r > 0 {
                            nb_valid = true;
                            nb = (r - 1) * n + c;
                        }
                    } else if pos == 1 {
                        if r + 1 < m {
                            nb_valid = true;
                            nb = (r + 1) * n + c;
                        }
                    } else if pos == 2 {
                        if c > 0 {
                            nb_valid = true;
                            nb = r * n + (c - 1);
                        }
                    } else {
                        if c + 1 < n {
                            nb_valid = true;
                            nb = r * n + (c + 1);
                        }
                    }

                    if nb_valid && grid[nb / n][nb % n] < cur_value {
                        if dp[nb] == -1 {
                            stack_ids.push(nb);
                            stack_pos.push(0);
                            stack_acc.push(1);
                        } else {
                            stack_acc[top] = (stack_acc[top] + dp[nb]) % modulo;
                            stack_pos[top] = pos + 1;
                        }
                    } else {
                        stack_pos[top] = pos + 1;
                    }
                }
            }
        }

        start += 1;
    }

    answer
}
