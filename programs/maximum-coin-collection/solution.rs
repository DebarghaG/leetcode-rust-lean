pub fn max_coins(lane1: &[i64], lane2: &[i64]) -> i64 {
    let n: usize = lane1.len();
    let neg_inf: i64 = -1000000000000000000;

    // s0: best path ending at previous mile, currently in lane 1, using 0 switches
    // s1: best path ending at previous mile, currently in lane 2, using 1 switch
    // s2: best path ending at previous mile, currently in lane 1, using 2 switches
    let mut s0: i64 = neg_inf;
    let mut s1: i64 = neg_inf;
    let mut s2: i64 = neg_inf;
    let mut ans: i64 = neg_inf;

    let mut i: usize = 0;
    while i < n {
        let a: i64 = lane1[i];
        let b: i64 = lane2[i];

        // Stay in lane 1 with 0 switches: either start here or extend.
        let mut ns0: i64 = a;
        let ext0: i64 = s0 + a;
        if ext0 > ns0 {
            ns0 = ext0;
        }

        // End in lane 2 with 1 switch:
        // start here with an immediate switch, extend lane 2, or switch from lane 1.
        let mut ns1: i64 = b;
        let ext1: i64 = s1 + b;
        if ext1 > ns1 {
            ns1 = ext1;
        }
        let sw01: i64 = s0 + b;
        if sw01 > ns1 {
            ns1 = sw01;
        }

        // End in lane 1 with 2 switches:
        // extend lane 1 after 2 switches, or switch from lane 2 after 1 switch.
        let ext2: i64 = s2 + a;
        let sw12: i64 = s1 + a;
        let mut ns2: i64 = ext2;
        if sw12 > ns2 {
            ns2 = sw12;
        }

        s0 = ns0;
        s1 = ns1;
        s2 = ns2;

        if s0 > ans {
            ans = s0;
        }
        if s1 > ans {
            ans = s1;
        }
        if s2 > ans {
            ans = s2;
        }

        i = i + 1;
    }

    ans
}
