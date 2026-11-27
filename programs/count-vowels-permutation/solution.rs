pub fn count_vowel_permutation(n: i64) -> i64 {
    let modulus: i64 = 1000000007;

    if n <= 0 {
        return 0;
    }

    // Counts of valid strings of current length ending in a, e, i, o, u.
    let mut a: i64 = 1;
    let mut e: i64 = 1;
    let mut i: i64 = 1;
    let mut o: i64 = 1;
    let mut u: i64 = 1;

    let mut step: i64 = 1;
    while step < n {
        let next_a = (e + i + u) % modulus;
        let next_e = (a + i) % modulus;
        let next_i = (e + o) % modulus;
        let next_o = i % modulus;
        let next_u = (i + o) % modulus;

        a = next_a;
        e = next_e;
        i = next_i;
        o = next_o;
        u = next_u;

        step += 1;
    }

    (a + e + i + o + u) % modulus
}
