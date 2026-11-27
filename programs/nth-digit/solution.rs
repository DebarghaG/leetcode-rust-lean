pub fn find_nth_digit(n: i64) -> i64 {
    let mut d: i64 = 1;
    let mut count: i64 = 9;
    let mut start: i64 = 1;
    let mut rem: i64 = n;

    while rem > d * count {
        rem = rem - d * count;
        d = d + 1;
        count = count * 10;
        start = start * 10;
    }

    let offset: i64 = rem - 1;
    let index: i64 = offset / d;
    let num: i64 = start + index;
    let pos: i64 = offset % d;

    let from_right: i64 = d - 1 - pos;
    let mut factor: i64 = 1;
    let mut k: i64 = 0;
    while k < from_right {
        factor = factor * 10;
        k = k + 1;
    }

    (num / factor) % 10
}
