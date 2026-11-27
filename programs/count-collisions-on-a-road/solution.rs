pub fn count_collisions(directions: &[u8]) -> i64 {
    let n = directions.len();

    let mut start: usize = 0;
    while start < n && directions[start] == b'L' {
        start += 1;
    }

    let mut end: usize = n;
    while end > start && directions[end - 1] == b'R' {
        end -= 1;
    }

    let mut ans: i64 = 0;
    let mut i: usize = start;

    while i < end {
        if directions[i] != b'S' {
            ans += 1;
        }
        i += 1;
    }

    ans
}
