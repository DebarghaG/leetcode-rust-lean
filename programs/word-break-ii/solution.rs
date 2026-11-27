#[allow(unused_macros)]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<Vec<u8>>::new()
    };
    ($($x:expr),+ $(,)?) => {{
        let mut __v: ::std::vec::Vec<_> = ::std::vec::Vec::new();
        $( __v.push($x); )+
        __v
    }};
}

fn wb_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn wb_lt(a: &[u8], b: &[u8]) -> bool {
    let mut i: usize = 0;
    while i < a.len() && i < b.len() {
        if a[i] < b[i] {
            return true;
        }
        if a[i] > b[i] {
            return false;
        }
        i += 1;
    }
    a.len() < b.len()
}

fn wb_matches(s: &[u8], pos: usize, w: &[u8]) -> bool {
    let m: usize = w.len();
    if m == 0 {
        return false;
    }
    if pos + m > s.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < m {
        if s[pos + i] != w[i] {
            return false;
        }
        i += 1;
    }
    true
}

#[allow(non_snake_case)]
pub fn word_break(s: &[u8], wordDict: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let n: usize = s.len();

    let mut words: Vec<Vec<u8>> = Vec::new();
    let mut d: usize = 0;
    while d < wordDict.len() {
        let w: &Vec<u8> = &wordDict[d];
        let mut dup: bool = false;
        let mut k: usize = 0;
        while k < words.len() {
            if wb_eq(&words[k], w) {
                dup = true;
            }
            k += 1;
        }
        if !dup {
            words.push(w.clone());
        }
        d += 1;
    }

    let mut dp: Vec<Vec<Vec<u8>>> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        let row: Vec<Vec<u8>> = Vec::new();
        dp.push(row);
        i += 1;
    }

    let base: Vec<u8> = Vec::new();
    dp[n].push(base);

    let mut pos: usize = n;
    while pos > 0 {
        pos -= 1;

        let mut wi: usize = 0;
        while wi < words.len() {
            let wl: usize = words[wi].len();
            if wl > 0 && pos + wl <= n && wb_matches(s, pos, &words[wi]) {
                let nxt: usize = pos + wl;
                let mut si: usize = 0;
                while si < dp[nxt].len() {
                    let mut sentence: Vec<u8> = words[wi].clone();
                    let sl: usize = dp[nxt][si].len();
                    if sl > 0 {
                        sentence.push(b' ');
                        let mut bi: usize = 0;
                        while bi < sl {
                            sentence.push(dp[nxt][si][bi]);
                            bi += 1;
                        }
                    }
                    dp[pos].push(sentence);
                    si += 1;
                }
            }
            wi += 1;
        }
    }

    let mut result: Vec<Vec<u8>> = dp[0].clone();
    let m: usize = result.len();
    let mut a: usize = 1;
    while a < m {
        let mut b: usize = a;
        while b > 0 {
            if wb_lt(&result[b], &result[b - 1]) {
                let tmp: Vec<u8> = result[b].clone();
                result[b] = result[b - 1].clone();
                result[b - 1] = tmp;
                b -= 1;
            } else {
                break;
            }
        }
        a += 1;
    }

    result
}
