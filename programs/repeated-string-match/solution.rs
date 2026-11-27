pub fn repeated_string_match(a: &[u8], b: &[u8]) -> i64 {
    let n = a.len();
    let m = b.len();

    if m == 0 {
        return 0;
    }
    if n == 0 {
        return -1;
    }

    let q = (m + n - 1) / n;

    let mut s: Vec<u8> = Vec::new();
    let mut i = 0usize;
    while i < q {
        let mut j = 0usize;
        while j < n {
            s.push(a[j]);
            j += 1;
        }
        i += 1;
    }

    if contains(&s, b) {
        return q as i64;
    }

    let mut j = 0usize;
    while j < n {
        s.push(a[j]);
        j += 1;
    }

    if contains(&s, b) {
        return (q as i64) + 1;
    }

    -1
}

fn contains(hay: &[u8], needle: &[u8]) -> bool {
    let n = hay.len();
    let m = needle.len();

    if m == 0 {
        return true;
    }
    if n < m {
        return false;
    }

    let last = n - m;
    let mut start = 0usize;

    while start <= last {
        if hay[start] == needle[0] {
            let mut j = 1usize;
            let mut ok = true;

            while j < m && ok {
                if hay[start + j] != needle[j] {
                    ok = false;
                } else {
                    j += 1;
                }
            }

            if ok {
                return true;
            }
        }

        start += 1;
    }

    false
}
