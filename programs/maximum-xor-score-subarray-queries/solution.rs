pub fn maximum_subarray_xor(nums: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = nums.len();

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut best: Vec<Vec<i64>> = Vec::new();

    let mut i = 0usize;
    while i < n {
        let mut row_dp: Vec<i64> = Vec::new();
        let mut row_best: Vec<i64> = Vec::new();

        let mut j = 0usize;
        while j < n {
            row_dp.push(0);
            row_best.push(0);
            j += 1;
        }

        dp.push(row_dp);
        best.push(row_best);
        i += 1;
    }

    let mut i = n;
    while i > 0 {
        i -= 1;

        dp[i][i] = nums[i];
        best[i][i] = nums[i];

        let mut j = i + 1;
        while j < n {
            let left = dp[i][j - 1];
            let down = dp[i + 1][j];
            let val = left ^ down;
            dp[i][j] = val;

            let mut m = val;
            let down_best = best[i + 1][j];
            let left_best = best[i][j - 1];

            if down_best > m {
                m = down_best;
            }
            if left_best > m {
                m = left_best;
            }

            best[i][j] = m;
            j += 1;
        }
    }

    let q = queries.len();
    let mut answer: Vec<i64> = Vec::new();

    let mut k = 0usize;
    while k < q {
        let l = queries[k][0] as usize;
        let r = queries[k][1] as usize;
        answer.push(best[l][r]);
        k += 1;
    }

    answer
}
