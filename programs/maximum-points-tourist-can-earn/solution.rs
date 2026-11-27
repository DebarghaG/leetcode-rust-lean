pub fn max_score(n: i64, k: i64, stayScore: &[Vec<i64>], travelScore: &[Vec<i64>]) -> i64 {
    let n_usize = n as usize;
    let k_usize = k as usize;

    let mut prev: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n_usize {
        prev.push(0);
        i += 1;
    }

    let mut day = 0usize;
    while day < k_usize {
        let mut curr: Vec<i64> = Vec::new();
        let mut dest = 0usize;
        while dest < n_usize {
            let mut best = prev[dest] + stayScore[day][dest];

            let mut from = 0usize;
            while from < n_usize {
                if from != dest {
                    let value = prev[from] + travelScore[from][dest];
                    if value > best {
                        best = value;
                    }
                }
                from += 1;
            }

            curr.push(best);
            dest += 1;
        }

        prev = curr;
        day += 1;
    }

    let mut ans: i64 = 0;
    let mut idx = 0usize;
    while idx < n_usize {
        if prev[idx] > ans {
            ans = prev[idx];
        }
        idx += 1;
    }

    ans
}
