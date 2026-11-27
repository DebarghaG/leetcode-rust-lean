fn window_matches(
    board: &[Vec<i64>],
    pattern: &[Vec<u8>],
    sr: usize,
    sc: usize,
) -> bool {
    let ph = pattern.len();
    let pw = pattern[0].len();

    let mut letter_to_digit: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < 26 {
        letter_to_digit.push(-1);
        k += 1;
    }

    let mut digit_used: Vec<bool> = Vec::new();
    k = 0;
    while k < 10 {
        digit_used.push(false);
        k += 1;
    }

    let mut ok = true;
    let mut i = 0;
    while i < ph && ok {
        let mut j = 0;
        while j < pw && ok {
            let pch = pattern[i][j];
            let val = board[sr + i][sc + j];

            if pch >= b'0' && pch <= b'9' {
                let d = (pch - b'0') as i64;
                if val != d {
                    ok = false;
                }
            } else if pch >= b'a' && pch <= b'z' {
                let idx = (pch - b'a') as usize;
                let mapped = letter_to_digit[idx];
                if mapped == -1 {
                    if val < 0 || val > 9 {
                        ok = false;
                    } else {
                        let vi = val as usize;
                        if digit_used[vi] {
                            ok = false;
                        } else {
                            letter_to_digit[idx] = val;
                            digit_used[vi] = true;
                        }
                    }
                } else {
                    if mapped != val {
                        ok = false;
                    }
                }
            } else {
                ok = false;
            }

            j += 1;
        }
        i += 1;
    }

    ok
}

pub fn find_pattern(board: &[Vec<i64>], pattern: &[Vec<u8>]) -> Vec<i64> {
    let n = board.len();
    let ph = pattern.len();

    let mut rr: i64 = -1;
    let mut cc: i64 = -1;

    if n > 0 && ph > 0 {
        let m = board[0].len();
        let pw = pattern[0].len();

        if pw > 0 && ph <= n && pw <= m {
            let mut found = false;
            let mut r = 0;
            while r + ph <= n && !found {
                let mut c = 0;
                while c + pw <= m && !found {
                    if window_matches(board, pattern, r, c) {
                        found = true;
                        rr = r as i64;
                        cc = c as i64;
                    }
                    c += 1;
                }
                r += 1;
            }
        }
    }

    let mut ans: Vec<i64> = Vec::new();
    ans.push(rr);
    ans.push(cc);
    ans
}
