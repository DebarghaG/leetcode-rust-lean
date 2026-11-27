pub fn min_time(skill: &[i64], mana: &[i64]) -> i64 {
    let n = skill.len();
    let m = mana.len();

    // pre[i] = sum of skill[0..i]
    let mut pre: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        pre.push(sum);
        sum += skill[i];
        i += 1;
    }

    // finish[i] = completion time of the latest potion at wizard i
    let mut finish: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        finish.push(0);
        i += 1;
    }

    let mut j: usize = 0;
    while j < m {
        let mana_j = mana[j];

        // Earliest possible start time of potion j.
        let mut start: i64 = finish[0];
        i = 1;
        while i < n {
            let candidate = finish[i] - pre[i] * mana_j;
            if candidate > start {
                start = candidate;
            }
            i += 1;
        }

        // Compute completion times for potion j.
        let mut acc: i64 = 0;
        i = 0;
        while i < n {
            acc += skill[i];
            finish[i] = start + acc * mana_j;
            i += 1;
        }

        j += 1;
    }

    finish[n - 1]
}
