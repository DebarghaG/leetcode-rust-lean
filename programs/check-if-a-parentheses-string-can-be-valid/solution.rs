pub fn can_be_valid(s: &[u8], locked: &[u8]) -> bool {
    let n = s.len();

    if n == 0 || n % 2 != 0 {
        return false;
    }

    let nl = locked.len();

    let mut ok: bool = true;
    let mut balance: i64 = 0;
    let mut i: usize = 0;

    // Left-to-right pass: treat every changeable position as '('.
    while i < n {
        let mut is_locked_close: bool = false;
        if i < nl {
            if locked[i] == b'1' && s[i] == b')' {
                is_locked_close = true;
            }
        }
        if is_locked_close {
            balance = balance - 1;
        } else {
            balance = balance + 1;
        }
        if balance < 0 {
            ok = false;
        }
        i += 1;
    }

    // Right-to-left pass: treat every changeable position as ')'.
    balance = 0;
    i = n;

    while i > 0 {
        i -= 1;
        let mut is_locked_open: bool = false;
        if i < nl {
            if locked[i] == b'1' && s[i] == b'(' {
                is_locked_open = true;
            }
        }
        if is_locked_open {
            balance = balance - 1;
        } else {
            balance = balance + 1;
        }
        if balance < 0 {
            ok = false;
        }
    }

    ok
}
