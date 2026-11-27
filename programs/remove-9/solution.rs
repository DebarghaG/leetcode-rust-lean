pub fn new_integer(n: i64) -> i64 {
    let mut x: i64 = n;
    let mut place: i64 = 1;
    let mut ans: i64 = 0;

    while x > 0 {
        let digit: i64 = x % 9;
        ans = ans + digit * place;
        x = x / 9;
        place = place * 10;
    }

    ans
}
