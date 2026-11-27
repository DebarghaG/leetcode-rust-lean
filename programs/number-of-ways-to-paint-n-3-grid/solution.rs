pub fn num_of_ways(n: i64) -> i64 {
    const MOD: i64 = 1_000_000_007;

    let mut same: i64 = 6;
    let mut diff: i64 = 6;

    let mut row: i64 = 2;
    while row <= n {
        let next_same = (3 * same + 2 * diff) % MOD;
        let next_diff = (2 * same + 2 * diff) % MOD;
        same = next_same;
        diff = next_diff;
        row += 1;
    }

    (same + diff) % MOD
}
