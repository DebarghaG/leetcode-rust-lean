pub fn lexical_order(n: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    if n <= 0 {
        return result;
    }

    let mut cur: i64 = 1;
    let mut count: i64 = 0;

    while count < n {
        result.push(cur);
        count += 1;

        if cur * 10 <= n {
            cur *= 10;
        } else if cur % 10 != 9 && cur + 1 <= n {
            cur += 1;
        } else {
            while (cur / 10) % 10 == 9 {
                cur /= 10;
            }
            cur = cur / 10 + 1;
        }
    }

    result
}
