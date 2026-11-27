fn ways_for_sum(m: i64) -> i64 {
    let k: i64 = m / 6 + 1;
    let parity: i64 = m % 2;
    let half_plus_one: i64 = (m - parity) / 2 + 1;
    let first: i64 = k * half_plus_one;
    let second: i64 = 3 * k * (k - 1) / 2;
    first - second
}

pub fn number_of_ways(n: i64) -> i64 {
    let modulo: i64 = 1_000_000_007;

    let mut ans: i64 = ways_for_sum(n);

    if n >= 4 {
        ans = ans + ways_for_sum(n - 4);
    }

    if n >= 8 {
        ans = ans + ways_for_sum(n - 8);
    }

    ans % modulo
}
