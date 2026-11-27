pub fn even_odd_bit(n: i64) -> Vec<i64> {
    let mut x = n;
    let mut idx = 0i64;
    let mut even = 0i64;
    let mut odd = 0i64;

    while x > 0 {
        if x % 2 == 1 {
            if idx % 2 == 0 {
                even += 1;
            } else {
                odd += 1;
            }
        }
        x = x / 2;
        idx += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(even);
    result.push(odd);
    result
}
