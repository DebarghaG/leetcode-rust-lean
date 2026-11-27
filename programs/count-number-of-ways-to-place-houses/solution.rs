pub fn count_house_placements(n: i64) -> i64 {
    let modulo: i64 = 1_000_000_007;

    // ways(0) = 1, ways(1) = 2
    // ways(k) = ways(k-1) + ways(k-2)
    let mut prev: i64 = 1;
    let mut cur: i64 = 2;

    let mut i: i64 = 1;
    while i < n {
        let next = (prev + cur) % modulo;
        prev = cur;
        cur = next;
        i += 1;
    }

    (cur * cur) % modulo
}
