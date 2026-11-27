pub fn diff_ways_to_compute(expression: &[u8]) -> Vec<i64> {
    let n = expression.len();
    let mut valid = true;

    if n == 0 {
        valid = false;
    }

    // Validate characters: only digits and '+', '-', '*'.
    let mut i = 0;
    while i < n {
        let c = expression[i];
        if c < b'0' || c > b'9' {
            if c != b'+' && c != b'-' && c != b'*' {
                valid = false;
            }
        }
        i += 1;
    }

    if !valid {
        return Vec::new();
    }

    // Parse into numbers and operators.
    let mut nums: Vec<i64> = Vec::new();
    let mut ops: Vec<u8> = Vec::new();

    let mut cur: i64 = 0;
    let mut in_num = false;
    let mut idx = 0;

    while idx < n {
        let c = expression[idx];
        if c >= b'0' && c <= b'9' {
            cur = cur * 10 + (c - b'0') as i64;
            in_num = true;
        } else {
            if !in_num {
                valid = false;
            }
            nums.push(cur);
            cur = 0;
            in_num = false;
            ops.push(c);
        }
        idx += 1;
    }

    if in_num {
        nums.push(cur);
    } else {
        valid = false;
    }

    if !valid {
        return Vec::new();
    }

    let count = nums.len();
    if count == 0 {
        return Vec::new();
    }
    if ops.len() + 1 != count {
        return Vec::new();
    }

    // dp[i][j] holds all results from combining nums[i..=j].
    let mut dp: Vec<Vec<Vec<i64>>> = Vec::new();
    let mut r = 0;
    while r < count {
        let mut row: Vec<Vec<i64>> = Vec::new();
        let mut c = 0;
        while c < count {
            let empty: Vec<i64> = Vec::new();
            row.push(empty);
            c += 1;
        }
        dp.push(row);
        r += 1;
    }

    let mut len = 1;
    while len <= count {
        let mut start = 0;
        while start + len <= count {
            let end = start + len - 1;

            if len == 1 {
                dp[start][end].push(nums[start]);
            } else {
                let mut k = start;
                while k < end {
                    let op = ops[k];
                    let left_len = dp[start][k].len();
                    let mut a = 0;
                    while a < left_len {
                        let left_val = dp[start][k][a];
                        let right_len = dp[k + 1][end].len();
                        let mut b = 0;
                        while b < right_len {
                            let right_val = dp[k + 1][end][b];
                            let val: i64 = if op == b'+' {
                                left_val + right_val
                            } else if op == b'-' {
                                left_val - right_val
                            } else {
                                left_val * right_val
                            };
                            dp[start][end].push(val);
                            b += 1;
                        }
                        a += 1;
                    }
                    k += 1;
                }
            }

            start += 1;
        }
        len += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut p = 0;
    while p < dp[0][count - 1].len() {
        result.push(dp[0][count - 1][p]);
        p += 1;
    }

    sort_i64(&mut result);
    result
}

fn sort_i64(v: &mut Vec<i64>) {
    let n = v.len();
    let mut i = 0;
    while i < n {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < n {
            if v[j] < v[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        if min_idx != i {
            let tmp = v[i];
            v[i] = v[min_idx];
            v[min_idx] = tmp;
        }
        i += 1;
    }
}
