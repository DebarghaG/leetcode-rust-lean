pub fn kth_grammar(n: i64, k: i64) -> i64 {
    let mut half: i64 = 1;
    let mut i: i64 = 2;
    while i < n {
        half = half * 2;
        i = i + 1;
    }

    let mut ans: i64 = 0;
    let mut nn: i64 = n;
    let mut kk: i64 = k;

    while nn > 1 {
        if kk > half {
            ans = 1 - ans;
            kk = kk - half;
        }
        half = half / 2;
        nn = nn - 1;
    }

    ans
}
