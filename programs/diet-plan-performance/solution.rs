pub fn diet_plan_performance(calories: &[i64], k: i64, lower: i64, upper: i64) -> i64 {
    let n = calories.len();
    let kk = k as usize;

    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < kk {
        sum += calories[i];
        i += 1;
    }

    let mut points: i64 = 0;
    if sum < lower {
        points -= 1;
    } else if sum > upper {
        points += 1;
    }

    let mut start: usize = 1;
    while start + kk <= n {
        sum = sum - calories[start - 1] + calories[start + kk - 1];

        if sum < lower {
            points -= 1;
        } else if sum > upper {
            points += 1;
        }

        start += 1;
    }

    points
}
