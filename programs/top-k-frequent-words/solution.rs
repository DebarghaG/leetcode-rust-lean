pub fn top_k_frequent(words: &[Vec<u8>], k: i64) -> Vec<Vec<u8>> {
    let n = words.len();

    let mut unique: Vec<Vec<u8>> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let w = &words[i];
        let un = unique.len();
        let mut found: usize = un;

        let mut j: usize = 0;
        while j < un {
            let mut eq = true;

            if unique[j].len() != w.len() {
                eq = false;
            } else {
                let mut t: usize = 0;
                while t < w.len() {
                    if unique[j][t] != w[t] {
                        eq = false;
                    }
                    t += 1;
                }
            }

            if eq {
                found = j;
            }
            j += 1;
        }

        if found == un {
            let mut copy: Vec<u8> = Vec::new();
            let mut t: usize = 0;
            while t < w.len() {
                copy.push(w[t]);
                t += 1;
            }
            unique.push(copy);
            counts.push(1);
        } else {
            let c = counts[found] + 1;
            counts[found] = c;
        }

        i += 1;
    }

    let uniq_n = unique.len();

    let mut used: Vec<bool> = Vec::new();
    let mut r: usize = 0;
    while r < uniq_n {
        used.push(false);
        r += 1;
    }

    let mut out: Vec<Vec<u8>> = Vec::new();

    let mut p: i64 = 0;
    while p < k {
        let mut best: usize = uniq_n;

        let mut j: usize = 0;
        while j < uniq_n {
            if !used[j] {
                if best == uniq_n {
                    best = j;
                } else {
                    let mut better = false;

                    if counts[j] > counts[best] {
                        better = true;
                    } else if counts[j] == counts[best] {
                        let a = &unique[j];
                        let b = &unique[best];

                        let mut q: usize = 0;
                        let mut diff: i64 = 0;

                        while q < a.len() && q < b.len() {
                            if diff == 0 {
                                if a[q] < b[q] {
                                    diff = -1;
                                } else if a[q] > b[q] {
                                    diff = 1;
                                }
                            }
                            q += 1;
                        }

                        if diff < 0 {
                            better = true;
                        } else if diff == 0 && a.len() < b.len() {
                            better = true;
                        }
                    }

                    if better {
                        best = j;
                    }
                }
            }
            j += 1;
        }

        if best != uniq_n {
            used[best] = true;

            let src = &unique[best];
            let mut row: Vec<u8> = Vec::new();
            let mut t: usize = 0;
            while t < src.len() {
                row.push(src[t]);
                t += 1;
            }
            out.push(row);
        }

        p += 1;
    }

    out
}
