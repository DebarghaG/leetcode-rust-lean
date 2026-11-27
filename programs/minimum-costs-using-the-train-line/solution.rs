pub fn minimum_costs(regular: &[i64], express: &[i64], express_cost: i64) -> Vec<i64> {
    let n: usize = regular.len();
    let mut costs: Vec<i64> = Vec::new();

    let mut reg: i64 = 0;
    let mut exp: i64 = express_cost;

    let mut i: usize = 0;
    while i < n {
        let r_cost: i64 = regular[i];
        let e_cost: i64 = express[i];

        let mut next_reg: i64 = reg + r_cost;
        let via_express: i64 = exp + e_cost;
        if via_express < next_reg {
            next_reg = via_express;
        }

        let mut next_exp: i64 = exp + e_cost;
        let transfer_from_reg: i64 = next_reg + express_cost;
        if transfer_from_reg < next_exp {
            next_exp = transfer_from_reg;
        }

        costs.push(next_reg);

        reg = next_reg;
        exp = next_exp;
        i += 1;
    }

    costs
}
