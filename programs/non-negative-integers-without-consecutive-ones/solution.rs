pub fn find_integers(n: i64) -> i64 {
    // g[k] = number of length-k binary strings with no two consecutive 1s.
    // g[0]=1, g[1]=2, g[k]=g[k-1]+g[k-2].  Precomputed up to k=30.
    let mut g: Vec<i64> = Vec::new();
    g.push(1);
    g.push(2);
    g.push(3);
    g.push(5);
    g.push(8);
    g.push(13);
    g.push(21);
    g.push(34);
    g.push(55);
    g.push(89);
    g.push(144);
    g.push(233);
    g.push(377);
    g.push(610);
    g.push(987);
    g.push(1597);
    g.push(2584);
    g.push(4181);
    g.push(6765);
    g.push(10946);
    g.push(17711);
    g.push(28657);
    g.push(46368);
    g.push(75025);
    g.push(121393);
    g.push(196418);
    g.push(317811);
    g.push(514229);
    g.push(832040);
    g.push(1346269);
    g.push(2178309);

    // Extract bits of n, MSB first, 31 entries (for 2^30 down to 2^0).
    let mut bits: Vec<i64> = Vec::new();
    let mut p: i64 = 1073741824; // 2^30
    while p > 0 {
        let b: i64 = (n / p) % 2;
        bits.push(b);
        p = p / 2;
    }

    // pre_ok[j] = 1 iff bits[0..j] contain no two consecutive ones.
    // pre_ok[0]=1, pre_ok[1]=1,
    // pre_ok[j] = pre_ok[j-1] * (1 - bits[j-1]*bits[j-2]) for j>=2.
    let mut okv: Vec<i64> = Vec::new();
    okv.push(1);
    okv.push(1);
    let mut i: usize = 2;
    while i < 32 {
        let len = okv.len();
        let prev: i64 = okv[len - 1];
        let pair: i64 = bits[i - 1] * bits[i - 2];
        okv.push(prev * (1 - pair));
        i = i + 1;
    }

    // Sum contributions: at position j (before a "11" occurs) with bit 1,
    // we can place a 0 here and fill the remaining (30-j) bits freely.
    let mut ans: i64 = 0;
    let mut j: usize = 0;
    while j < 31 {
        ans = ans + okv[j] * bits[j] * g[30 - j];
        j = j + 1;
    }

    // If n itself has no consecutive ones, count it too.
    ans = ans + okv[31];
    ans
}
