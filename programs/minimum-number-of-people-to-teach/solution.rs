pub fn minimum_teachings(n: i64, languages: &[Vec<i64>], friendships: &[Vec<i64>]) -> i64 {
    let m = languages.len();

    let mut need: Vec<bool> = Vec::new();
    let mut idx: usize = 0;
    while idx < m {
        need.push(false);
        idx += 1;
    }

    let mut f: usize = 0;
    while f < friendships.len() {
        let u = (friendships[f][0] - 1) as usize;
        let v = (friendships[f][1] - 1) as usize;

        let lu = &languages[u];
        let lv = &languages[v];

        let mut common: bool = false;
        let mut i: usize = 0;
        while i < lu.len() {
            let mut j: usize = 0;
            while j < lv.len() {
                if lu[i] == lv[j] {
                    common = true;
                }
                j += 1;
            }
            i += 1;
        }

        if !common {
            need[u] = true;
            need[v] = true;
        }

        f += 1;
    }

    let mut best: i64 = m as i64 + 1;
    let mut lang: i64 = 1;
    while lang <= n {
        let mut count: i64 = 0;
        let mut u: usize = 0;
        while u < m {
            if need[u] {
                let lu = &languages[u];
                let mut knows: bool = false;
                let mut k: usize = 0;
                while k < lu.len() {
                    if lu[k] == lang {
                        knows = true;
                    }
                    k += 1;
                }

                if !knows {
                    count += 1;
                }
            }
            u += 1;
        }

        if count < best {
            best = count;
        }

        lang += 1;
    }

    best
}
