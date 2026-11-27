pub fn distribute_candies(candies: i64, num_people: i64) -> Vec<i64> {
    let n = num_people as usize;
    let mut ans: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        ans.push(0);
        i += 1;
    }

    let mut remaining = candies;
    let mut give = 1i64;
    let mut idx = 0usize;

    while remaining > 0 {
        let mut amount = give;
        if amount > remaining {
            amount = remaining;
        }

        ans[idx] = ans[idx] + amount;
        remaining -= amount;
        give += 1;

        idx += 1;
        if idx == n {
            idx = 0;
        }
    }

    ans
}
