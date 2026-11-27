pub fn count_triplets(arr: &[i64]) -> i64 {
    let n = arr.len();

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    let mut cur: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        cur = cur ^ arr[i];
        prefix.push(cur);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut x: usize = 0;
    while x <= n {
        let mut y: usize = x + 1;
        while y <= n {
            if prefix[x] == prefix[y] {
                let mut d: usize = y - x - 1;
                while d > 0 {
                    ans += 1;
                    d -= 1;
                }
            }
            y += 1;
        }
        x += 1;
    }

    ans
}
