pub fn shortest_sequence(rolls: &[i64], k: i64) -> i64 {
    let n: usize = rolls.len();

    // One-sided die: every sequence is a run of 1s (all of them present),
    // so the shortest impossible sequence is just longer than the whole array.
    if k <= 1 {
        return n as i64 + 1;
    }

    // Fewer rolls than faces: some face never occurs, so a length-1
    // sequence using that face is impossible.
    if k > n as i64 {
        return 1;
    }

    // Now 2 <= k <= n, so a seen-array of size k+1 is proportional to input.
    let kk: usize = k as usize;
    let mut seen: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j <= kk {
        seen.push(0);
        j += 1;
    }

    // Greedy: each time we collect all k distinct values, that's one
    // "complete round". The answer is (number of complete rounds) + 1.
    // `stamp` lets us skip clearing `seen` between rounds.
    let mut stamp: i64 = 1;
    let mut distinct: i64 = 0;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let v: i64 = rolls[i];
        if v >= 1 && v <= k {
            let idx: usize = v as usize;
            if seen[idx] != stamp {
                seen[idx] = stamp;
                distinct += 1;
                if distinct == k {
                    ans += 1;
                    distinct = 0;
                    stamp += 1;
                }
            }
        }
        i += 1;
    }

    ans + 1
}
