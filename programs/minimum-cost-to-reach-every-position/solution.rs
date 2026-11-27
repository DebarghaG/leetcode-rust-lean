pub fn min_costs(cost: &[i64]) -> Vec<i64> {
    let mut answer: Vec<i64> = Vec::new();
    let n = cost.len();

    if n == 0 {
        return answer;
    }

    let mut best = cost[0];
    let mut i = 0usize;

    while i < n {
        if cost[i] < best {
            best = cost[i];
        }
        answer.push(best);
        i += 1;
    }

    answer
}
