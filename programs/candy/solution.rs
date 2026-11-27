pub fn candy(ratings: &[i64]) -> i64 {
    let n = ratings.len();
    if n == 0 {
        return 0;
    }

    let mut candies: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        candies.push(1);
        i += 1;
    }

    i = 1;
    while i < n {
        if ratings[i] > ratings[i - 1] {
            candies[i] = candies[i - 1] + 1;
        }
        i += 1;
    }

    i = n - 1;
    while i > 0 {
        if ratings[i - 1] > ratings[i] && candies[i - 1] <= candies[i] {
            candies[i - 1] = candies[i] + 1;
        }
        i -= 1;
    }

    let mut total: i64 = 0;
    i = 0;
    while i < n {
        total += candies[i];
        i += 1;
    }

    total
}
