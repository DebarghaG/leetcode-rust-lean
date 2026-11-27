pub fn min_cost_climbing_stairs(cost: &[i64]) -> i64 {
    let n = cost.len();

    let mut prev2 = cost[0];
    let mut prev1 = cost[1];

    let mut i: usize = 2;
    while i < n {
        let better = if prev1 < prev2 { prev1 } else { prev2 };
        let cur = cost[i] + better;

        prev2 = prev1;
        prev1 = cur;

        i += 1;
    }

    if prev1 < prev2 { prev1 } else { prev2 }
}
