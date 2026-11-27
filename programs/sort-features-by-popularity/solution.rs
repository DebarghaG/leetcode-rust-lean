pub fn sort_features(features: &[Vec<u8>], responses: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let n = features.len();
    let rn = responses.len();

    // pop[i] = number of responses containing feature i (at least once).
    let mut pop: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        pop.push(0);
        i += 1;
    }

    // For each feature, scan every response and test whether it contains the
    // feature as a whole word. Stop scanning a response at the first match so
    // the feature is counted at most once per response.
    i = 0;
    while i < n {
        let fl = features[i].len();
        let mut r: usize = 0;
        while r < rn {
            let len = responses[r].len();
            let mut pos: usize = 0;
            let mut found: bool = false;

            while pos < len && !found {
                let start = pos;
                let mut end = pos;
                while end < len && responses[r][end] != b' ' {
                    end += 1;
                }
                let wl = end - start;

                if wl == fl {
                    let mut same: bool = true;
                    let mut k: usize = 0;
                    while k < fl {
                        if responses[r][start + k] != features[i][k] {
                            same = false;
                        }
                        k += 1;
                    }
                    if same {
                        found = true;
                    }
                }

                pos = end;
                if pos < len && responses[r][pos] == b' ' {
                    pos += 1;
                }
            }

            if found {
                pop[i] += 1;
            }
            r += 1;
        }
        i += 1;
    }

    // Selection sort: repeatedly pick the unused feature with the highest
    // popularity; ties resolved by smallest original index (natural because we
    // scan indices in increasing order and only replace on strictly greater pop).
    let mut used: Vec<bool> = Vec::new();
    i = 0;
    while i < n {
        used.push(false);
        i += 1;
    }

    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut step: usize = 0;
    while step < n {
        let mut best: i64 = -1;
        let mut j: usize = 0;
        while j < n {
            if !used[j] {
                if best < 0 {
                    best = j as i64;
                } else {
                    let b = best as usize;
                    if pop[j] > pop[b] {
                        best = j as i64;
                    }
                }
            }
            j += 1;
        }

        let b = best as usize;
        used[b] = true;

        let mut word: Vec<u8> = Vec::new();
        let mut k: usize = 0;
        while k < features[b].len() {
            word.push(features[b][k]);
            k += 1;
        }
        out.push(word);

        step += 1;
    }

    out
}
