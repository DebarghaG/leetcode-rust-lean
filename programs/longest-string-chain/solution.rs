pub fn longest_str_chain(words: &[Vec<u8>]) -> i64 {
    let n = words.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dp.push(1);
        i = i + 1;
    }

    let mut max_len: usize = 0;
    i = 0;
    while i < n {
        let l = words[i].len();
        if l > max_len {
            max_len = l;
        }
        i = i + 1;
    }

    let mut length: usize = 2;
    while length <= max_len {
        let mut wi: usize = 0;
        while wi < n {
            if words[wi].len() == length {
                let cur = &words[wi];
                let mut best: i64 = 1;

                let mut pi: usize = 0;
                while pi < n {
                    if words[pi].len() + 1 == length {
                        let prev = &words[pi];

                        let mut p: usize = 0;
                        let mut q: usize = 0;
                        let mut skipped: bool = false;
                        let mut ok: bool = true;

                        while q < cur.len() {
                            if p < prev.len() && prev[p] == cur[q] {
                                p = p + 1;
                                q = q + 1;
                            } else if !skipped {
                                skipped = true;
                                q = q + 1;
                            } else {
                                ok = false;
                                break;
                            }
                        }

                        if ok && skipped && p == prev.len() {
                            let cand = dp[pi] + 1;
                            if cand > best {
                                best = cand;
                            }
                        }
                    }
                    pi = pi + 1;
                }

                dp[wi] = best;
            }
            wi = wi + 1;
        }
        length = length + 1;
    }

    let mut ans: i64 = 1;
    i = 0;
    while i < n {
        if dp[i] > ans {
            ans = dp[i];
        }
        i = i + 1;
    }
    ans
}
