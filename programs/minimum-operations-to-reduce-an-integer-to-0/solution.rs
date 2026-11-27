pub fn min_operations(n: i64) -> i64 {
    let mut x: i64 = n;
    let mut ans: i64 = 0;

    while x > 0 {
        if x % 2 == 1 {
            if x % 4 == 3 {
                x += 1;
            } else {
                x -= 1;
            }
            ans += 1;
        } else {
            x = x / 2;
        }
    }

    ans
}
