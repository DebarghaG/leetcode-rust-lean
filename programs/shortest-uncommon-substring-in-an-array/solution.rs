fn occurs(haystack: &Vec<u8>, needle: &Vec<u8>) -> bool {
    let h = haystack.len();
    let m = needle.len();
    if m == 0 {
        return true;
    }
    if m > h {
        return false;
    }
    let maxp = h - m;
    let mut p = 0usize;
    while p <= maxp {
        let mut k = 0usize;
        let mut same = true;
        while k < m {
            if haystack[p + k] != needle[k] {
                same = false;
                break;
            }
            k += 1;
        }
        if same {
            return true;
        }
        p += 1;
    }
    false
}

fn lex_less(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    let la = a.len();
    let lb = b.len();
    let m = if la < lb { la } else { lb };
    let mut k = 0usize;
    while k < m {
        if a[k] < b[k] {
            return true;
        }
        if a[k] > b[k] {
            return false;
        }
        k += 1;
    }
    la < lb
}

pub fn shortest_substrings(arr: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let n = arr.len();
    let mut ans: Vec<Vec<u8>> = Vec::new();

    let mut i = 0usize;
    while i < n {
        let mut best: Vec<u8> = Vec::new();
        let s = &arr[i];
        let l = s.len();
        let mut len = 1usize;

        while len <= l {
            let mut have = false;
            let mut best_cand: Vec<u8> = Vec::new();
            let max_start = l - len;
            let mut st = 0usize;

            while st <= max_start {
                let mut cand: Vec<u8> = Vec::new();
                let mut k = 0usize;
                while k < len {
                    cand.push(s[st + k]);
                    k += 1;
                }

                let mut elsewhere = false;
                let mut j = 0usize;
                while j < n {
                    if j != i {
                        if occurs(&arr[j], &cand) {
                            elsewhere = true;
                            break;
                        }
                    }
                    j += 1;
                }

                if !elsewhere {
                    if !have {
                        best_cand = cand;
                        have = true;
                    } else if lex_less(&cand, &best_cand) {
                        best_cand = cand;
                    }
                }

                st += 1;
            }

            if have {
                best = best_cand;
                break;
            }

            len += 1;
        }

        ans.push(best);
        i += 1;
    }

    ans
}
