pub fn most_points(questions: &[Vec<i64>]) -> i64 {
    let n = questions.len();
    let mut dp: Vec<i64> = Vec::new();

    let mut k = 0usize;
    while k <= n {
        dp.push(0);
        k += 1;
    }

    let mut i = n;
    while i > 0 {
        i -= 1;

        let points = questions[i][0];
        let brainpower = questions[i][1] as usize;

        let mut next = i + brainpower + 1;
        if next > n {
            next = n;
        }

        let skip = dp[i + 1];
        let take = points + dp[next];

        if take > skip {
            dp[i] = take;
        } else {
            dp[i] = skip;
        }
    }

    dp[0]
}
