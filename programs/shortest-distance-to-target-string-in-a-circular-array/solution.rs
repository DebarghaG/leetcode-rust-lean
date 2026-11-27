pub fn closest_target(words: &[Vec<u8>], target: &[u8], startIndex: i64) -> i64 {
    let n = words.len();
    let n_i = n as i64;
    let mut ans: i64 = -1;

    let mut i: usize = 0;
    while i < n {
        let w = &words[i];
        let w_len = w.len();
        let mut same = true;

        if w_len != target.len() {
            same = false;
        } else {
            let mut j: usize = 0;
            while j < w_len {
                if w[j] != target[j] {
                    same = false;
                }
                j += 1;
            }
        }

        if same {
            let mut d: i64 = i as i64 - startIndex;
            if d < 0 {
                d = -d;
            }

            let back = n_i - d;
            let mut cur = d;
            if back < cur {
                cur = back;
            }

            if ans == -1 {
                ans = cur;
            } else if cur < ans {
                ans = cur;
            }
        }

        i += 1;
    }

    ans
}
