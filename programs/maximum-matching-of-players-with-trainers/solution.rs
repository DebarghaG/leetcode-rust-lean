fn sort_copy(xs: &[i64]) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < xs.len() {
        v.push(xs[k]);
        k = k + 1;
    }

    let n = v.len();
    let mut i: usize = 1;
    while i < n {
        let key = v[i];
        let mut j: usize = i;
        while j > 0 && v[j - 1] > key {
            let prev = v[j - 1];
            v[j] = prev;
            j = j - 1;
        }
        v[j] = key;
        i = i + 1;
    }

    v
}

pub fn match_players_and_trainers(players: &[i64], trainers: &[i64]) -> i64 {
    let ps = sort_copy(players);
    let ts = sort_copy(trainers);

    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut ans: i64 = 0;

    while i < ps.len() && j < ts.len() {
        if ps[i] <= ts[j] {
            ans = ans + 1;
            i = i + 1;
            j = j + 1;
        } else {
            j = j + 1;
        }
    }

    ans
}
