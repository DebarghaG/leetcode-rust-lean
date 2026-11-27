pub fn make_array_increasing(arr1: &[i64], arr2: &[i64]) -> i64 {
    let n = arr1.len();
    let m0 = arr2.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < m0 {
        sorted.push(arr2[idx]);
        idx += 1;
    }

    let mut pos: usize = 1;
    while pos < sorted.len() {
        let key = sorted[pos];
        let mut q: usize = pos;
        while q > 0 && sorted[q - 1] > key {
            sorted[q] = sorted[q - 1];
            q -= 1;
        }
        sorted[q] = key;
        pos += 1;
    }

    let mut b: Vec<i64> = Vec::new();
    let mut idx2: usize = 0;
    while idx2 < sorted.len() {
        if idx2 == 0 {
            b.push(sorted[idx2]);
        } else {
            if sorted[idx2] != sorted[idx2 - 1] {
                b.push(sorted[idx2]);
            }
        }
        idx2 += 1;
    }

    let m = b.len();
    let inf: i64 = 1000000000;

    if n == 0 {
        return 0;
    }

    let mut dkeep: i64 = 0;
    let mut dprepl: Vec<i64> = Vec::new();
    let mut jj: usize = 0;
    while jj < m {
        dprepl.push(1);
        jj += 1;
    }

    let mut i: usize = 1;
    while i < n {
        let a_prev = arr1[i - 1];
        let a_cur = arr1[i];

        let mut newkeep = inf;
        if a_cur > a_prev && dkeep < newkeep {
            newkeep = dkeep;
        }

        let mut j: usize = 0;
        while j < m {
            if a_cur > b[j] && dprepl[j] < newkeep {
                newkeep = dprepl[j];
            }
            j += 1;
        }

        let mut newrepl: Vec<i64> = Vec::new();
        let mut best_prev_repl: i64 = inf;
        let mut k: usize = 0;
        while k < m {
            let mut v = inf;

            if b[k] > a_prev && dkeep < inf {
                let cand = dkeep + 1;
                if cand < v {
                    v = cand;
                }
            }

            if best_prev_repl < inf {
                let cand2 = best_prev_repl + 1;
                if cand2 < v {
                    v = cand2;
                }
            }

            newrepl.push(v);

            if dprepl[k] < best_prev_repl {
                best_prev_repl = dprepl[k];
            }

            k += 1;
        }

        dkeep = newkeep;
        dprepl = newrepl;
        i += 1;
    }

    let mut ans = dkeep;
    let mut t: usize = 0;
    while t < m {
        if dprepl[t] < ans {
            ans = dprepl[t];
        }
        t += 1;
    }

    if ans >= inf {
        -1
    } else {
        ans
    }
}
