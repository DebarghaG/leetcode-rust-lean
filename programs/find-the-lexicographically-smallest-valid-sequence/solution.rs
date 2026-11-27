pub fn valid_sequence(word1: &[u8], word2: &[u8]) -> Vec<i64> {
    let n = word1.len();
    let m = word2.len();

    if m > n {
        return Vec::new();
    }

    // suf[i] = maximum L such that word2[m-L..m] is a subsequence
    // of word1[i..] using exact matches.
    let mut suf: Vec<i64> = Vec::new();
    // one[i] = maximum L such that word2[m-L..m] is a subsequence
    // of word1[i..] allowing at most one mismatching character.
    let mut one: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k <= n {
        suf.push(0);
        one.push(0);
        k += 1;
    }

    let m_i: i64 = m as i64;

    let mut i: usize = n;
    while i > 0 {
        i -= 1;

        let e_next: i64 = suf[i + 1];
        if e_next < m_i {
            let need: usize = (m_i - e_next - 1) as usize;
            if word1[i] == word2[need] {
                suf[i] = e_next + 1;
            } else {
                suf[i] = e_next;
            }
        } else {
            suf[i] = e_next;
        }

        let o_next: i64 = one[i + 1];
        let mut best: i64 = o_next;

        if e_next < m_i {
            let cand: i64 = e_next + 1;
            if cand > best {
                best = cand;
            }
        }

        if o_next < m_i {
            let need2: usize = (m_i - o_next - 1) as usize;
            if word1[i] == word2[need2] {
                let cand2: i64 = o_next + 1;
                if cand2 > best {
                    best = cand2;
                }
            }
        }

        one[i] = best;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut used_mismatch: bool = false;
    let mut pos: usize = 0;
    let mut j: usize = 0;

    while j < m {
        let rem: i64 = (m - j - 1) as i64;
        let mut found: bool = false;
        let mut chosen: usize = 0;

        let mut p: usize = pos;
        while p < n {
            let c: u8 = word1[p];
            let target: u8 = word2[j];
            let mut ok: bool = false;

            if !used_mismatch {
                if c == target {
                    if one[p + 1] >= rem {
                        ok = true;
                    }
                } else {
                    if suf[p + 1] >= rem {
                        ok = true;
                    }
                }
            } else {
                if c == target && suf[p + 1] >= rem {
                    ok = true;
                }
            }

            if ok {
                chosen = p;
                found = true;
                if !used_mismatch && c != target {
                    used_mismatch = true;
                }
                break;
            }

            p += 1;
        }

        if !found {
            return Vec::new();
        }

        ans.push(chosen as i64);
        pos = chosen + 1;
        j += 1;
    }

    ans
}
