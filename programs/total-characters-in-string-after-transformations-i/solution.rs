fn letter_at(p: usize) -> u8 {
    if p == 0 {
        b'a'
    } else if p == 1 {
        b'b'
    } else if p == 2 {
        b'c'
    } else if p == 3 {
        b'd'
    } else if p == 4 {
        b'e'
    } else if p == 5 {
        b'f'
    } else if p == 6 {
        b'g'
    } else if p == 7 {
        b'h'
    } else if p == 8 {
        b'i'
    } else if p == 9 {
        b'j'
    } else if p == 10 {
        b'k'
    } else if p == 11 {
        b'l'
    } else if p == 12 {
        b'm'
    } else if p == 13 {
        b'n'
    } else if p == 14 {
        b'o'
    } else if p == 15 {
        b'p'
    } else if p == 16 {
        b'q'
    } else if p == 17 {
        b'r'
    } else if p == 18 {
        b's'
    } else if p == 19 {
        b't'
    } else if p == 20 {
        b'u'
    } else if p == 21 {
        b'v'
    } else if p == 22 {
        b'w'
    } else if p == 23 {
        b'x'
    } else if p == 24 {
        b'y'
    } else {
        b'z'
    }
}

pub fn length_after_transformations(s: &[u8], t: i64) -> i64 {
    let md: i64 = 1000000007;

    let mut counts: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < 26 {
        let target: u8 = letter_at(p);

        let mut c: i64 = 0;
        let mut i: usize = 0;
        while i < s.len() {
            if s[i] == target {
                c += 1;
            }
            i += 1;
        }

        counts.push(c % md);
        p += 1;
    }

    let mut step: i64 = 0;
    while step < t {
        let z: i64 = counts[25];

        let mut next: Vec<i64> = Vec::new();
        next.push(z);
        next.push((counts[0] + z) % md);

        let mut j: usize = 2;
        while j < 26 {
            next.push(counts[j - 1]);
            j += 1;
        }

        counts = next;
        step += 1;
    }

    let mut ans: i64 = 0;
    let mut k: usize = 0;
    while k < 26 {
        ans = (ans + counts[k]) % md;
        k += 1;
    }

    ans
}
