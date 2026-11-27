pub fn stone_game_viii(stones: &[i64]) -> i64 {
    let n = stones.len();

    let mut prefix: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        sum += stones[i];
        prefix.push(sum);
        i += 1;
    }

    let mut ans: i64 = prefix[n - 1];
    let mut j: usize = n - 2;

    while j >= 1 {
        let candidate = prefix[j] - ans;
        if candidate > ans {
            ans = candidate;
        }
        j -= 1;
    }

    ans
}
