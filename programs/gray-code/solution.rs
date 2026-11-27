pub fn gray_code(n: i64) -> Vec<i64> {
    let mut total: i64 = 1;
    let mut k: i64 = 0;
    while k < n {
        total = total * 2;
        k = k + 1;
    }

    let mut out: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < total {
        let value: i64 = i ^ (i >> 1);
        out.push(value);
        i = i + 1;
    }

    out
}
