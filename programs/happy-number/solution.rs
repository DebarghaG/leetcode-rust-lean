pub fn is_happy(n: i64) -> bool {
    let mut slow = n;
    let mut fast = digit_square_sum(n);

    while fast != 1 && slow != fast {
        slow = digit_square_sum(slow);
        fast = digit_square_sum(digit_square_sum(fast));
    }

    fast == 1
}

fn digit_square_sum(mut x: i64) -> i64 {
    let mut sum: i64 = 0;

    while x > 0 {
        let d: i64 = x % 10;
        sum += d * d;
        x = x / 10;
    }

    sum
}
