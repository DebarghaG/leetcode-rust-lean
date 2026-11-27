pub fn climb_stairs(n: i64) -> i64 {
    if n == 1 {
        return 1;
    }
    if n == 2 {
        return 2;
    }

    let mut prev: i64 = 1;
    let mut cur: i64 = 2;
    let mut i: i64 = 3;

    while i <= n {
        let next: i64 = prev + cur;
        prev = cur;
        cur = next;
        i = i + 1;
    }

    cur
}
