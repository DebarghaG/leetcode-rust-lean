pub fn min_distance(word1: &[u8], word2: &[u8]) -> i64 {
    let n = word1.len();
    let m = word2.len();

    let mut prev: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j <= m {
        prev.push(j as i64);
        j += 1;
    }

    let mut i: usize = 1;
    while i <= n {
        let mut cur: Vec<i64> = Vec::new();
        cur.push(i as i64);

        let mut j: usize = 1;
        while j <= m {
            let cost: i64 = if word1[i - 1] == word2[j - 1] { 0 } else { 1 };

            let delete_cost = prev[j] + 1;
            let insert_cost = cur[j - 1] + 1;
            let replace_cost = prev[j - 1] + cost;

            let mut best = delete_cost;
            if insert_cost < best {
                best = insert_cost;
            }
            if replace_cost < best {
                best = replace_cost;
            }

            cur.push(best);
            j += 1;
        }

        prev = cur;
        i += 1;
    }

    prev[m]
}
