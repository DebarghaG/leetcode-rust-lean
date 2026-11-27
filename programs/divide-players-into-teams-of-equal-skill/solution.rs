pub fn divide_players(skill: &[i64]) -> i64 {
    let n = skill.len();
    if n == 0 {
        return 0;
    }
    if n % 2 != 0 {
        return -1;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 1001 {
        counts.push(0);
        i += 1;
    }

    let mut ok: bool = true;

    i = 0;
    while i < n {
        let x = skill[i];
        if x < 0 || x > 1000 {
            ok = false;
        }
        if ok {
            let idx = x as usize;
            counts[idx] = counts[idx] + 1;
        }
        i += 1;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut value: i64 = 0;
    while value <= 1000 {
        let idx = value as usize;
        let c = counts[idx];
        let mut j: i64 = 0;
        while j < c {
            sorted.push(value);
            j += 1;
        }
        value += 1;
    }

    let mut left: usize = 0;
    let mut right: usize = n - 1;
    let mut target: i64 = -1;
    let mut ans: i64 = 0;

    while left < right && ok {
        let team_sum = sorted[left] + sorted[right];
        if target == -1 {
            target = team_sum;
        } else if team_sum != target {
            ok = false;
        }
        if ok {
            ans += sorted[left] * sorted[right];
        }
        left += 1;
        right -= 1;
    }

    if !ok {
        return -1;
    }

    ans
}
