pub fn valid_strings(n: i64) -> Vec<Vec<u8>> {
    let mut cur: Vec<Vec<u8>> = Vec::new();
    let empty: Vec<u8> = Vec::new();
    cur.push(empty);

    let mut pos: i64 = 0;
    while pos < n {
        let mut next: Vec<Vec<u8>> = Vec::new();
        let count = cur.len();
        let mut i: usize = 0;

        while i < count {
            let plen = cur[i].len();

            let mut can_zero = true;
            if plen > 0 {
                if cur[i][plen - 1] == b'0' {
                    can_zero = false;
                }
            }

            if can_zero {
                let mut s: Vec<u8> = Vec::new();
                let mut j: usize = 0;
                while j < plen {
                    s.push(cur[i][j]);
                    j += 1;
                }
                s.push(b'0');
                next.push(s);
            }

            let mut s1: Vec<u8> = Vec::new();
            let mut j1: usize = 0;
            while j1 < plen {
                s1.push(cur[i][j1]);
                j1 += 1;
            }
            s1.push(b'1');
            next.push(s1);

            i += 1;
        }

        cur = next;
        pos += 1;
    }

    cur
}
