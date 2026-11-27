fn name_key(code: &[u8], start: usize, end: usize) -> i64 {
    let len = end - start;
    let mut result: i64 = -1;
    if len >= 1 && len <= 9 {
        let mut val: i64 = 0;
        let mut ok: bool = true;
        let mut k = start;
        while k < end {
            let b = code[k];
            if b < b'A' || b > b'Z' {
                ok = false;
            } else {
                let d: i64 = (b - b'A') as i64;
                val = val * 26 + d;
            }
            k = k + 1;
        }
        if ok {
            let cnt: i64 = (end - start) as i64;
            result = val * 10 + cnt;
        }
    }
    result
}

pub fn is_valid(code: &[u8]) -> bool {
    let n = code.len();
    let mut stack: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut ok: bool = true;

    while i < n && ok {
        if i > 0 && stack.len() == 0 {
            ok = false;
        } else if code[i] != b'<' {
            i = i + 1;
        } else {
            let mut is_cdata = false;
            if i + 9 <= n {
                if code[i + 1] == b'!'
                    && code[i + 2] == b'['
                    && code[i + 3] == b'C'
                    && code[i + 4] == b'D'
                    && code[i + 5] == b'A'
                    && code[i + 6] == b'T'
                    && code[i + 7] == b'A'
                    && code[i + 8] == b'['
                {
                    is_cdata = true;
                }
            }

            if is_cdata {
                let mut j = i + 9;
                let mut found = false;
                while !found && j + 2 < n {
                    if code[j] == b']' && code[j + 1] == b']' && code[j + 2] == b'>' {
                        found = true;
                    } else {
                        j = j + 1;
                    }
                }
                if found {
                    i = j + 3;
                } else {
                    ok = false;
                }
            } else if i + 1 < n && code[i + 1] == b'/' {
                let mut j = i + 2;
                while j < n && code[j] != b'>' {
                    j = j + 1;
                }
                if j == n {
                    ok = false;
                } else {
                    let key = name_key(code, i + 2, j);
                    if key < 0 {
                        ok = false;
                    } else if stack.len() == 0 {
                        ok = false;
                    } else if stack[stack.len() - 1] != key {
                        ok = false;
                    } else {
                        stack.pop();
                        i = j + 1;
                    }
                }
            } else {
                let mut j = i + 1;
                while j < n && code[j] != b'>' {
                    j = j + 1;
                }
                if j == n {
                    ok = false;
                } else {
                    let key = name_key(code, i + 1, j);
                    if key < 0 {
                        ok = false;
                    } else {
                        stack.push(key);
                        i = j + 1;
                    }
                }
            }
        }
    }

    ok && stack.len() == 0 && n > 0
}
