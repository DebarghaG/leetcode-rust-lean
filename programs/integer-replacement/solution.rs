pub fn integer_replacement(n: i64) -> i64 {
    let mut x: i64 = n;
    let mut steps: i64 = 0;

    while x > 1 {
        if x % 2 == 0 {
            x = x / 2;
            steps = steps + 1;
        } else {
            if x == 3 {
                steps = steps + 2;
                x = 1;
            } else if x % 4 == 1 {
                x = x - 1;
                steps = steps + 1;
            } else {
                x = x + 1;
                steps = steps + 1;
            }
        }
    }

    steps
}
