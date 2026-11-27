pub fn can_eat(candiesCount: &[i64], queries: &[Vec<i64>]) -> Vec<bool> {
    let n = candiesCount.len();

    let mut prefix: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        prefix.push(sum);
        sum = sum + candiesCount[i];
        i = i + 1;
    }
    prefix.push(sum);

    let qn = queries.len();
    let mut answer: Vec<bool> = Vec::new();
    let mut qi: usize = 0;

    while qi < qn {
        let favorite_type = queries[qi][0];
        let favorite_day = queries[qi][1];
        let daily_cap = queries[qi][2];

        let f = favorite_type as usize;

        let before = prefix[f];
        let through = prefix[f + 1];

        let max_eaten_by_day = (favorite_day + 1) * daily_cap;

        let mut ok = true;

        if max_eaten_by_day < before + 1 {
            ok = false;
        }

        if favorite_day >= through {
            ok = false;
        }

        answer.push(ok);
        qi = qi + 1;
    }

    answer
}
