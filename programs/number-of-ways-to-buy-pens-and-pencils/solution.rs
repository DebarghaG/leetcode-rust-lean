pub fn ways_to_buy_pens_pencils(total: i64, cost1: i64, cost2: i64) -> i64 {
    let mut ways: i64 = 0;
    let mut paid_for_pens: i64 = 0;

    while paid_for_pens <= total {
        let remaining: i64 = total - paid_for_pens;
        ways += remaining / cost2 + 1;
        paid_for_pens += cost1;
    }

    ways
}
