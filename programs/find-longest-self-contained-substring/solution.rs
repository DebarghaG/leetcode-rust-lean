pub fn max_substring_length(s: &[u8]) -> i64 {
    let n = s.len();

    let mut first: Vec<i64> = Vec::new();
    let mut last: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < 26 {
        first.push(-1);
        last.push(-1);
        i += 1;
    }

    i = 0;
    while i < n {
        let idx = (s[i] - b'a') as usize;
        if first[idx] == -1 {
            first[idx] = i as i64;
        }
        last[idx] = i as i64;
        i += 1;
    }

    let mut ans: i64 = -1;

    let mut c = 0;
    while c < 26 {
        if first[c] != -1 {
            let l_i = first[c];
            let l = l_i as usize;

            let mut d = 0;
            while d < 26 {
                if last[d] != -1 {
                    let r_i = last[d];

                    if l_i <= r_i {
                        let len = r_i - l_i + 1;
                        let is_whole = (l_i == 0) && (r_i == (n as i64) - 1);

                        if !is_whole && len > ans {
                            let r = r_i as usize;
                            let mut ok = true;
                            let mut p = l;

                            while p <= r && ok {
                                let idx = (s[p] - b'a') as usize;
                                if first[idx] < l_i || last[idx] > r_i {
                                    ok = false;
                                }
                                p += 1;
                            }

                            if ok {
                                ans = len;
                            }
                        }
                    }
                }
                d += 1;
            }
        }
        c += 1;
    }

    ans
}
