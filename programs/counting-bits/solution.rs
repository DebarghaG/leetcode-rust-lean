pub fn count_bits(n: i64) -> Vec<i64> {
    if n < 0 {
        return Vec::new();
    }

    let mut ans: Vec<i64> = Vec::new();
    ans.push(0);

    let n_usize = n as usize;
    let mut i: usize = 1;

    while i <= n_usize {
        let prev = ans[i / 2];
        let bit = (i % 2) as i64;
        ans.push(prev + bit);
        i += 1;
    }

    ans
}
