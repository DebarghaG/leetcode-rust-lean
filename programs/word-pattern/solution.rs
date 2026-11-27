pub fn word_pattern(pattern: &[u8], s: &[u8]) -> bool {
    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < s.len() {
        if s[i] == b' ' {
            i += 1;
        } else {
            let st: usize = i;
            while i < s.len() && s[i] != b' ' {
                i += 1;
            }
            starts.push(st as i64);
            ends.push(i as i64);
        }
    }

    let n: usize = pattern.len();
    let cnt: usize = starts.len();
    let mut ok: bool = cnt == n;

    if ok {
        let mut a: usize = 0;
        while a < n {
            let mut b: usize = 0;
            while b < a {
                let same_pattern: bool = pattern[a] == pattern[b];
                let same_word: bool =
                    word_eq(s, starts[a], ends[a], starts[b], ends[b]);
                if same_pattern != same_word {
                    ok = false;
                    b = a;
                } else {
                    b += 1;
                }
            }
            if !ok {
                a = n;
            } else {
                a += 1;
            }
        }
    }

    ok
}

fn word_eq(s: &[u8], a0: i64, a1: i64, b0: i64, b1: i64) -> bool {
    let len_a: usize = (a1 - a0) as usize;
    let len_b: usize = (b1 - b0) as usize;
    let mut eq: bool = len_a == len_b;

    if eq {
        let mut k: usize = 0;
        while k < len_a {
            let ca: u8 = s[(a0 as usize) + k];
            let cb: u8 = s[(b0 as usize) + k];
            if ca != cb {
                eq = false;
                k = len_a;
            } else {
                k += 1;
            }
        }
    }

    eq
}
