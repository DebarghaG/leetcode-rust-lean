pub fn is_reachable(targetX: i64, targetY: i64) -> bool {
    let mut a: i64 = targetX;
    let mut b: i64 = targetY;

    while b != 0 {
        let r: i64 = a % b;
        a = b;
        b = r;
    }

    let mut g: i64 = a;
    while g > 1 && g % 2 == 0 {
        g = g / 2;
    }

    g == 1
}
