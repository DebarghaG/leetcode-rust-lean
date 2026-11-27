pub fn count_servers(n: i64, logs: &[Vec<i64>], x: i64, queries: &[i64]) -> Vec<i64> {
    let base = n + 1;
    let m = logs.len();

    let mut log_keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        let server = logs[i][0];
        let time = logs[i][1];
        log_keys.push(time * base + server);
        i += 1;
    }
    log_keys.sort();

    let qlen = queries.len();
    let qn = qlen as i64;

    let mut qkeys: Vec<i64> = Vec::new();
    i = 0;
    while i < qlen {
        qkeys.push(queries[i] * qn + (i as i64));
        i += 1;
    }
    qkeys.sort();

    let nn = n as usize;
    let mut counts: Vec<i64> = Vec::new();
    i = 0;
    while i <= nn {
        counts.push(0);
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    i = 0;
    while i < qlen {
        ans.push(0);
        i += 1;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut distinct: i64 = 0;

    let mut qi: usize = 0;
    while qi < qlen {
        let qkey = qkeys[qi];
        let q = qkey / qn;
        let idx = (qkey % qn) as usize;

        while right < m {
            let t = log_keys[right] / base;
            if t > q {
                break;
            }

            let s = (log_keys[right] % base) as usize;
            if counts[s] == 0 {
                distinct += 1;
            }
            counts[s] += 1;
            right += 1;
        }

        let lower = q - x;
        while left < right {
            let t = log_keys[left] / base;
            if t >= lower {
                break;
            }

            let s = (log_keys[left] % base) as usize;
            if counts[s] == 1 {
                distinct -= 1;
            }
            counts[s] -= 1;
            left += 1;
        }

        ans[idx] = n - distinct;
        qi += 1;
    }

    ans
}
