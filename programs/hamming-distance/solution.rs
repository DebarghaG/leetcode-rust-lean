pub fn hamming_distance(x: i64, y: i64) -> i64 {
    let mut z: i64 = x ^ y;
    let mut count: i64 = 0;

    while z > 0 {
        count += z & 1;
        z = z >> 1;
    }

    count
}
