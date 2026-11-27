pub fn num_decodings(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let md: i64 = 1000000007;

    let first = s[0];
    let mut prev2: i64 = 1;
    let mut prev1: i64 = 0;

    if first == b'*' {
        prev1 = 9;
    } else if first == b'0' {
        prev1 = 0;
    } else {
        prev1 = 1;
    }

    if n == 1 {
        return prev1;
    }

    let mut i: usize = 2;
    while i <= n {
        let c1 = s[i - 2];
        let c2 = s[i - 1];

        let mut one: i64 = 0;
        if c2 == b'*' {
            one = 9;
        } else if c2 != b'0' {
            one = 1;
        }

        let mut two: i64 = 0;
        if c1 == b'*' {
            if c2 == b'*' {
                two = 15;
            } else if c2 <= b'6' {
                two = 2;
            } else {
                two = 1;
            }
        } else if c2 == b'*' {
            if c1 == b'1' {
                two = 9;
            } else if c1 == b'2' {
                two = 6;
            }
        } else {
            if c1 == b'1' {
                two = 1;
            } else if c1 == b'2' {
                if c2 <= b'6' {
                    two = 1;
                }
            }
        }

        let cur = (prev1 * one + prev2 * two) % md;
        prev2 = prev1;
        prev1 = cur;
        i = i + 1;
    }

    prev1
}
