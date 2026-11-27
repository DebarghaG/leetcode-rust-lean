pub fn min_bit_flips(start: i64, goal: i64) -> i64 {
    let mut a = start;
    let mut b = goal;
    let mut count: i64 = 0;
    while a > 0 || b > 0 {
        let ra = a % 2;
        let rb = b % 2;
        if ra != rb {
            count += 1;
        }
        a = a / 2;
        b = b / 2;
    }
    count
}
