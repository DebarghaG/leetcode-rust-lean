pub fn max_upgrades(count: &[i64], upgrade: &[i64], sell: &[i64], money: &[i64]) -> Vec<i64> {
    let n = count.len();
    let mut answer: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let c = count[i];
        let total_money = money[i] + c * sell[i];
        let cost_per_upgrade = upgrade[i] + sell[i];

        let mut upgraded = total_money / cost_per_upgrade;
        if upgraded > c {
            upgraded = c;
        }

        answer.push(upgraded);
        i += 1;
    }

    answer
}
