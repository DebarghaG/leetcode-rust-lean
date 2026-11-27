pub fn count_triples(n: i64) -> i64 {
    let mut count: i64 = 0;
    let mut a: i64 = 1;

    while a <= n {
        let mut b: i64 = 1;
        while b <= n {
            let target = a * a + b * b;

            let mut c: i64 = 1;
            while c <= n && c * c < target {
                c += 1;
            }

            if c <= n && c * c == target {
                count += 1;
            }

            b += 1;
        }
        a += 1;
    }

    count
}
