pub fn balanced_string(s: &[u8]) -> i64 {
    let n: usize = s.len();
    let target: i64 = (n as i64) / 4;

    let mut cq: i64 = 0;
    let mut cw: i64 = 0;
    let mut ce: i64 = 0;
    let mut cr: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let ch: u8 = s[i];
        if ch == b'Q' {
            cq += 1;
        } else if ch == b'W' {
            cw += 1;
        } else if ch == b'E' {
            ce += 1;
        } else if ch == b'R' {
            cr += 1;
        }
        i += 1;
    }

    if cq <= target && cw <= target && ce <= target && cr <= target {
        return 0;
    }

    let mut ans: i64 = n as i64;
    let mut left: usize = 0;
    let mut right: usize = 0;

    while right < n {
        let ch: u8 = s[right];
        if ch == b'Q' {
            cq -= 1;
        } else if ch == b'W' {
            cw -= 1;
        } else if ch == b'E' {
            ce -= 1;
        } else if ch == b'R' {
            cr -= 1;
        }

        while left <= right {
            if cq <= target && cw <= target && ce <= target && cr <= target {
                let len: i64 = (right - left + 1) as i64;
                if len < ans {
                    ans = len;
                }

                let lch: u8 = s[left];
                if lch == b'Q' {
                    cq += 1;
                } else if lch == b'W' {
                    cw += 1;
                } else if lch == b'E' {
                    ce += 1;
                } else if lch == b'R' {
                    cr += 1;
                }

                left += 1;
            } else {
                break;
            }
        }

        right += 1;
    }

    ans
}
