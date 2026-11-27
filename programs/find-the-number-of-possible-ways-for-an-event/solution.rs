pub fn number_of_ways(n: i64, x: i64, y: i64) -> i64 {
    let m: i64 = 1000000007;

    let mut n_us: usize = 0;
    let mut t: i64 = 0;
    while t < n {
        n_us += 1;
        t += 1;
    }

    let mut x_us: usize = 0;
    t = 0;
    while t < x {
        x_us += 1;
        t += 1;
    }

    let mut maxk: usize = n_us;
    if x_us < maxk {
        maxk = x_us;
    }

    // prev[k] = Stirling number S(i, k) for the current row i.
    let mut prev: Vec<i64> = Vec::new();
    prev.push(1);
    let mut j: usize = 1;
    while j <= maxk {
        prev.push(0);
        j += 1;
    }

    let mut i: usize = 1;
    while i <= n_us {
        let mut next: Vec<i64> = Vec::new();
        next.push(0);

        let mut k_us: usize = 1;
        let mut km1: usize = 0;
        let mut k_i: i64 = 1;

        while k_us <= maxk {
            let a: i64 = prev[km1];
            let b: i64 = (k_i * prev[k_us]) % m;
            let v: i64 = (a + b) % m;
            next.push(v);

            k_us += 1;
            km1 += 1;
            k_i += 1;
        }

        prev = next;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut falling: i64 = 1;
    let mut power: i64 = 1;

    let mut k_us: usize = 1;
    let mut k_i: i64 = 1;

    while k_us <= maxk {
        falling = (falling * (x - k_i + 1)) % m;
        power = (power * y) % m;

        let term: i64 = (prev[k_us] * falling) % m;
        let term2: i64 = (term * power) % m;
        ans = (ans + term2) % m;

        k_us += 1;
        k_i += 1;
    }

    ans
}
