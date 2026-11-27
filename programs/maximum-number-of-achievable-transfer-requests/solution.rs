pub fn maximum_requests(n: i64, requests: &[Vec<i64>]) -> i64 {
    let m: usize = requests.len();
    let n_usize: usize = n as usize;
    let m_i64: i64 = m as i64;

    let mut total: usize = 1;
    let mut e: usize = 0;
    while e < m {
        total = total * 2;
        e += 1;
    }

    let mut balances: Vec<i64> = Vec::new();
    let mut b: usize = 0;
    while b < n_usize {
        balances.push(0);
        b += 1;
    }

    let mut best: i64 = 0;
    let mut mask: usize = 0;

    while mask < total {
        let mut i: usize = 0;
        while i < n_usize {
            balances[i] = 0;
            i += 1;
        }

        let mut count: i64 = 0;
        let mut j: usize = 0;
        while j < m {
            if ((mask >> j) & 1) == 1 {
                let from_idx: usize = requests[j][0] as usize;
                let to_idx: usize = requests[j][1] as usize;
                balances[from_idx] = balances[from_idx] - 1;
                balances[to_idx] = balances[to_idx] + 1;
                count += 1;
            }
            j += 1;
        }

        if count > best {
            let mut ok: bool = true;
            let mut k: usize = 0;
            while k < n_usize {
                if balances[k] != 0 {
                    ok = false;
                }
                k += 1;
            }

            if ok {
                best = count;
                if best == m_i64 {
                    return best;
                }
            }
        }

        mask += 1;
    }

    best
}
