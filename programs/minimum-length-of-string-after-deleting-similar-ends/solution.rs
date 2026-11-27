pub fn minimum_length(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut i: usize = 0;
    let mut j: usize = n - 1;

    while i < j {
        if s[i] != s[j] {
            break;
        }

        let c = s[i];

        while i <= j {
            if s[i] != c {
                break;
            }
            i += 1;
        }

        while i <= j {
            if s[j] != c {
                break;
            }
            if j == 0 {
                break;
            }
            j -= 1;
        }
    }

    if i > j {
        0
    } else {
        (j - i + 1) as i64
    }
}
