pub fn is_palindrome(x: i64) -> bool {
    if x < 0 {
        return false;
    }
    if x != 0 && x % 10 == 0 {
        return false;
    }

    let mut n: i64 = x;
    let mut reversed: i64 = 0;

    while n > reversed {
        reversed = reversed * 10 + n % 10;
        n = n / 10;
    }

    n == reversed || n == reversed / 10
}
