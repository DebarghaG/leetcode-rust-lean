fn compute_grundy(n: usize) -> Vec<i64> {
    let mut g: Vec<i64> = Vec::new();
    g.push(0);
    if n >= 1 {
        g.push(0);
    }

    let mut len = 2;
    while len <= n {
        let mut seen: Vec<bool> = Vec::new();
        let mut t = 0;
        while t < 256 {
            seen.push(false);
            t += 1;
        }

        let mut a = 0;
        while a + 1 < len {
            let b = len - 2 - a;
            let val = g[a] ^ g[b];
            if val < 256 {
                seen[val as usize] = true;
            }
            a += 1;
        }

        let mut mex = 0;
        while mex < 256 && seen[mex] {
            mex += 1;
        }

        g.push(mex as i64);
        len += 1;
    }

    g
}

pub fn can_win(currentState: &[u8]) -> bool {
    let n = currentState.len();
    let g = compute_grundy(n);

    let mut xor_sum: i64 = 0;
    let mut i = 0;

    while i < n {
        if currentState[i] == b'+' {
            let start = i;
            while i < n && currentState[i] == b'+' {
                i += 1;
            }
            let run_len = i - start;
            xor_sum = xor_sum ^ g[run_len];
        } else {
            i += 1;
        }
    }

    xor_sum != 0
}
