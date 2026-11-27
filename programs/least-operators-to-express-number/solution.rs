pub fn least_ops_express_target(x: i64, target: i64) -> i64 {
    if target == 0 {
        return 0;
    }

    let mut t = target;
    let mut dp0: i64 = 0;
    let mut dp1: i64 = 1000000000000000;
    let mut i: i64 = 0;

    while t > 0 {
        let q = t / x;
        let r = t - q * x;
        t = q;

        let w = if i == 0 { 2 } else { i };

        let n0a = dp0 + r * w;
        let n0b = dp1 + (r + 1) * w;
        let n0 = if n0a < n0b { n0a } else { n0b };

        let n1a = dp0 + (x - r) * w;
        let n1b = dp1 + (x - r - 1) * w;
        let n1 = if n1a < n1b { n1a } else { n1b };

        dp0 = n0;
        dp1 = n1;
        i = i + 1;
    }

    let ans0 = dp0 - 1;
    let ans1 = dp1 + i - 1;

    if ans0 < ans1 { ans0 } else { ans1 }
}
