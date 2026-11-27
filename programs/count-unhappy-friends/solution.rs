pub fn unhappy_friends(n: i64, preferences: &[Vec<i64>], pairs: &[Vec<i64>]) -> i64 {
    let nn = n as usize;

    let mut partner: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < nn {
        partner.push(-1);
        i += 1;
    }

    let mut p = 0usize;
    while p < pairs.len() {
        let a = pairs[p][0];
        let b = pairs[p][1];
        partner[a as usize] = b;
        partner[b as usize] = a;
        p += 1;
    }

    let sentinel = n + 1;
    let mut rank: Vec<Vec<i64>> = Vec::new();

    i = 0usize;
    while i < nn {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < nn {
            row.push(sentinel);
            j += 1;
        }

        let prefs_i = &preferences[i];
        let mut k = 0usize;
        while k < prefs_i.len() {
            let person = prefs_i[k];
            row[person as usize] = k as i64;
            k += 1;
        }

        rank.push(row);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut x = 0usize;

    while x < nn {
        let y = partner[x];
        let prefs_x = &preferences[x];

        let mut j = 0usize;
        let mut finished = false;

        while j < prefs_x.len() && !finished {
            let u = prefs_x[j];

            if u == y {
                finished = true;
            } else {
                let v = partner[u as usize];
                let rank_u = &rank[u as usize];

                if rank_u[x] < rank_u[v as usize] {
                    ans += 1;
                    finished = true;
                } else {
                    j += 1;
                }
            }
        }

        x += 1;
    }

    ans
}
