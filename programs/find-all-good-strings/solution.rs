const MOD: i64 = 1000000007;

fn count_leq(bound: &[u8], trans: &[Vec<i64>], m: usize, len: usize) -> i64 {
    let mut less: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        less.push(0);
        i += 1;
    }

    let mut tight_valid: bool = true;
    let mut tight_state: usize = 0;
    let mut pos: usize = 0;

    while pos < len {
        let mut next: Vec<i64> = Vec::new();
        let mut z: usize = 0;
        while z < m {
            next.push(0);
            z += 1;
        }

        let mut s: usize = 0;
        while s < m {
            let val: i64 = less[s];
            if val != 0 {
                let mut c: usize = 0;
                while c < 26 {
                    let ns_val: i64 = trans[s][c];
                    if ns_val >= 0 {
                        let ns: usize = ns_val as usize;
                        let sum: i64 = next[ns] + val;
                        next[ns] = sum % MOD;
                    }
                    c += 1;
                }
            }
            s += 1;
        }

        if tight_valid {
            let limit: usize = (bound[pos] - b'a') as usize;

            let mut c: usize = 0;
            while c < limit {
                let ns_val: i64 = trans[tight_state][c];
                if ns_val >= 0 {
                    let ns: usize = ns_val as usize;
                    let sum: i64 = next[ns] + 1;
                    next[ns] = sum % MOD;
                }
                c += 1;
            }

            let eq_val: i64 = trans[tight_state][limit];
            if eq_val >= 0 {
                tight_state = eq_val as usize;
            } else {
                tight_valid = false;
            }
        }

        less = next;
        pos += 1;
    }

    let mut ans: i64 = 0;
    let mut s: usize = 0;
    while s < m {
        ans = (ans + less[s]) % MOD;
        s += 1;
    }

    if tight_valid {
        ans = (ans + 1) % MOD;
    }

    ans
}

pub fn find_good_strings(n: i64, s1: &[u8], s2: &[u8], evil: &[u8]) -> i64 {
    let m: usize = evil.len();
    let n_usize: usize = n as usize;

    let mut pi: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        pi.push(0);
        i += 1;
    }

    let mut j: usize = 0;
    i = 1;
    while i < m {
        while j > 0 && evil[i] != evil[j] {
            j = pi[j - 1];
        }
        if evil[i] == evil[j] {
            j += 1;
        }
        pi[i] = j;
        i += 1;
    }

    let mut trans: Vec<Vec<i64>> = Vec::new();
    let mut st: usize = 0;
    while st < m {
        let mut row: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < 26 {
            let ch: u8 = 97u8 + (c as u8);

            let mut k: usize = st;
            while k > 0 && evil[k] != ch {
                k = pi[k - 1];
            }
            if evil[k] == ch {
                k += 1;
            }

            if k == m {
                row.push(-1);
            } else {
                row.push(k as i64);
            }

            c += 1;
        }
        trans.push(row);
        st += 1;
    }

    let hi: i64 = count_leq(s2, &trans, m, n_usize);
    let lo: i64 = count_leq(s1, &trans, m, n_usize);

    let mut good_s1: i64 = 1;
    let mut state: usize = 0;
    let mut pos: usize = 0;
    while pos < n_usize {
        let c: usize = (s1[pos] - b'a') as usize;
        let next_val: i64 = trans[state][c];
        if next_val < 0 {
            good_s1 = 0;
            break;
        }
        state = next_val as usize;
        pos += 1;
    }

    let mut ans: i64 = (hi - lo) % MOD;
    if ans < 0 {
        ans += MOD;
    }
    ans = (ans + good_s1) % MOD;

    ans
}
