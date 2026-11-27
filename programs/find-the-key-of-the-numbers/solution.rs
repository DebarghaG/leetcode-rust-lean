pub fn generate_key(num1: i64, num2: i64, num3: i64) -> i64 {
    let mut key: i64 = 0;
    let mut place: i64 = 1000;

    while place >= 1 {
        let d1: i64 = (num1 / place) % 10;
        let d2: i64 = (num2 / place) % 10;
        let d3: i64 = (num3 / place) % 10;

        let mut m: i64 = d1;
        if d2 < m {
            m = d2;
        }
        if d3 < m {
            m = d3;
        }

        key = key * 10 + m;
        place = place / 10;
    }

    key
}
