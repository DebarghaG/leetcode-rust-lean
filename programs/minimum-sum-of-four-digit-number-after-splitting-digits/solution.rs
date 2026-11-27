pub fn minimum_sum(num: i64) -> i64 {
    let mut d0: i64 = num / 1000;
    let mut d1: i64 = (num / 100) % 10;
    let mut d2: i64 = (num / 10) % 10;
    let mut d3: i64 = num % 10;

    if d0 > d1 {
        let t = d0;
        d0 = d1;
        d1 = t;
    }
    if d2 > d3 {
        let t = d2;
        d2 = d3;
        d3 = t;
    }
    if d0 > d2 {
        let t = d0;
        d0 = d2;
        d2 = t;
    }
    if d1 > d3 {
        let t = d1;
        d1 = d3;
        d3 = t;
    }
    if d1 > d2 {
        let t = d1;
        d1 = d2;
        d2 = t;
    }

    (d0 + d1) * 10 + d2 + d3
}
