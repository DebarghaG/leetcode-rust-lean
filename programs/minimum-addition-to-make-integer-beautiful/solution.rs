fn digit_sum(mut x: i64) -> i64 {
    let mut s: i64 = 0;
    while x > 0 {
        s += x % 10;
        x /= 10;
    }
    s
}

pub fn make_integer_beautiful(n: i64, target: i64) -> i64 {
    let mut ans: i64 = 0;
    let mut base: i64 = 1;

    while digit_sum(n + ans) > target {
        let cur: i64 = n + ans;
        let digit: i64 = (cur / base) % 10;
        let add: i64 = if digit == 0 {
            0
        } else {
            (10 - digit) * base
        };

        ans += add;
        base *= 10;
    }

    ans
}
