pub fn max_num_of_substrings(s: &[u8]) -> Vec<Vec<u8>> {
    let n = s.len();

    let mut first: Vec<usize> = Vec::new();
    let mut last: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < 26 {
        first.push(n);
        last.push(0);
        i += 1;
    }

    let mut pos = 0;
    while pos < n {
        let c = (s[pos] - b'a') as usize;
        if first[c] == n {
            first[c] = pos;
        }
        last[c] = pos;
        pos += 1;
    }

    let mut adj: Vec<bool> = Vec::new();
    let mut idx = 0;
    while idx < 676 {
        adj.push(false);
        idx += 1;
    }

    let mut c = 0;
    while c < 26 {
        if first[c] < n {
            let mut j = first[c];
            let r = last[c];
            while j <= r {
                let d = (s[j] - b'a') as usize;
                adj[c * 26 + d] = true;
                j += 1;
            }
        }
        c += 1;
    }

    let mut cand_l: Vec<usize> = Vec::new();
    let mut cand_r: Vec<usize> = Vec::new();

    c = 0;
    while c < 26 {
        if first[c] < n {
            let mut reach: Vec<bool> = Vec::new();
            let mut k = 0;
            while k < 26 {
                reach.push(false);
                k += 1;
            }
            reach[c] = true;

            let mut changed = true;
            while changed {
                changed = false;
                let mut a = 0;
                while a < 26 {
                    if reach[a] {
                        let mut d = 0;
                        while d < 26 {
                            if adj[a * 26 + d] && !reach[d] {
                                reach[d] = true;
                                changed = true;
                            }
                            d += 1;
                        }
                    }
                    a += 1;
                }
            }

            let mut l = n;
            let mut r = 0;
            let mut d = 0;
            while d < 26 {
                if reach[d] {
                    if first[d] < l {
                        l = first[d];
                    }
                    if last[d] > r {
                        r = last[d];
                    }
                }
                d += 1;
            }

            cand_l.push(l);
            cand_r.push(r);
        }
        c += 1;
    }

    let m = cand_l.len();
    let mut i = 0;
    while i < m {
        let mut best = i;
        let mut j = i + 1;
        while j < m {
            if cand_r[j] < cand_r[best]
                || (cand_r[j] == cand_r[best] && cand_l[j] > cand_l[best])
            {
                best = j;
            }
            j += 1;
        }

        if best != i {
            let tmp_l = cand_l[i];
            cand_l[i] = cand_l[best];
            cand_l[best] = tmp_l;

            let tmp_r = cand_r[i];
            cand_r[i] = cand_r[best];
            cand_r[best] = tmp_r;
        }

        i += 1;
    }

    let mut ans: Vec<Vec<u8>> = Vec::new();
    let mut has_last = false;
    let mut last_end: usize = 0;

    let mut i = 0;
    while i < m {
        let l = cand_l[i];
        let r = cand_r[i];

        if !has_last || l > last_end {
            let mut piece: Vec<u8> = Vec::new();
            let mut k = l;
            while k <= r {
                piece.push(s[k]);
                k += 1;
            }
            ans.push(piece);
            last_end = r;
            has_last = true;
        }

        i += 1;
    }

    ans
}
