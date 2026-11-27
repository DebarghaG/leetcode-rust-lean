pub fn word_pattern_match(pattern: &[u8], s: &[u8]) -> bool {
    let n = pattern.len();
    let m = s.len();

    // map[c] is the string currently assigned to byte c.
    // An empty Vec means c is still unassigned.
    let mut map: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    while i < 256 {
        map.push(Vec::new());
        i += 1;
    }

    // Explicit backtracking stack. Each frame records an unmapped pattern
    // position whose chosen length may need to be increased on backtracking.
    let mut stack_pi: Vec<i64> = Vec::new();
    let mut stack_si: Vec<i64> = Vec::new();
    let mut stack_idx: Vec<i64> = Vec::new();
    let mut stack_len: Vec<i64> = Vec::new();

    let mut pi: usize = 0;
    let mut si: usize = 0;

    loop {
        let mut failed = false;

        if pi == n {
            if si == m {
                return true;
            }
            failed = true;
        } else {
            let idx = pattern[pi] as usize;
            let mlen = map[idx].len();

            if mlen > 0 {
                let mut ok = true;
                if si + mlen > m {
                    ok = false;
                } else {
                    let mut j = 0;
                    while j < mlen {
                        if s[si + j] != map[idx][j] {
                            ok = false;
                            break;
                        }
                        j += 1;
                    }
                }

                if ok {
                    pi += 1;
                    si += mlen;
                } else {
                    failed = true;
                }
            } else {
                let mut chosen = false;
                let mut len: usize = 1;

                while len <= m - si {
                    if !is_used(&map, s, si, len) {
                        let mut cand: Vec<u8> = Vec::new();
                        let mut j = 0;
                        while j < len {
                            cand.push(s[si + j]);
                            j += 1;
                        }

                        map[idx] = cand;
                        stack_pi.push(pi as i64);
                        stack_si.push(si as i64);
                        stack_idx.push(idx as i64);
                        stack_len.push(len as i64);

                        pi += 1;
                        si += len;
                        chosen = true;
                        break;
                    }
                    len += 1;
                }

                if !chosen {
                    failed = true;
                }
            }
        }

        if failed {
            let mut backtracked = false;

            while stack_pi.len() > 0 {
                let last = stack_pi.len() - 1;
                let fpi = stack_pi[last] as usize;
                let fsi = stack_si[last] as usize;
                let fidx = stack_idx[last] as usize;
                let flen = stack_len[last] as usize;

                map[fidx] = Vec::new();

                stack_pi.pop();
                stack_si.pop();
                stack_idx.pop();
                stack_len.pop();

                let mut len = flen + 1;
                while len <= m - fsi {
                    if !is_used(&map, s, fsi, len) {
                        let mut cand: Vec<u8> = Vec::new();
                        let mut j = 0;
                        while j < len {
                            cand.push(s[fsi + j]);
                            j += 1;
                        }

                        map[fidx] = cand;
                        stack_pi.push(fpi as i64);
                        stack_si.push(fsi as i64);
                        stack_idx.push(fidx as i64);
                        stack_len.push(len as i64);

                        pi = fpi + 1;
                        si = fsi + len;
                        backtracked = true;
                        break;
                    }
                    len += 1;
                }

                if backtracked {
                    break;
                }
            }

            if !backtracked {
                return false;
            }
        }
    }
}

fn is_used(map: &[Vec<u8>], s: &[u8], start: usize, len: usize) -> bool {
    if len == 0 {
        return false;
    }

    let mut k = 0;
    while k < map.len() {
        let mlen = map[k].len();
        if mlen == len {
            let mut j = 0;
            let mut same = true;
            while j < len {
                if map[k][j] != s[start + j] {
                    same = false;
                    break;
                }
                j += 1;
            }
            if same {
                return true;
            }
        }
        k += 1;
    }

    false
}
