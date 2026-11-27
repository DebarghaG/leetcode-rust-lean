pub fn poor_pigs(buckets: i64, minutesToDie: i64, minutesToTest: i64) -> i64 {
    let base: i64 = minutesToTest / minutesToDie + 1;
    let mut pigs: i64 = 0;
    let mut capacity: i64 = 1;

    while capacity < buckets {
        capacity = capacity * base;
        pigs += 1;
    }

    pigs
}
