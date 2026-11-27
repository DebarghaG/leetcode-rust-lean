pub fn max_jump(stones: &[i64]) -> i64 {
    let n = stones.len();
    let mut ans = stones[1] - stones[0];
    let mut i: usize = 0;

    while i + 2 < n {
        let jump = stones[i + 2] - stones[i];
        if jump > ans {
            ans = jump;
        }
        i += 1;
    }

    ans
}
