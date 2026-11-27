pub fn min_cost(colors: &[u8], neededTime: &[i64]) -> i64 {
    let n = colors.len();
    if n == 0 {
        return 0;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let c = colors[i];
        let mut run_sum: i64 = neededTime[i];
        let mut run_max: i64 = neededTime[i];
        let mut j: usize = i + 1;

        while j < n {
            if colors[j] != c {
                break;
            }

            run_sum += neededTime[j];
            if neededTime[j] > run_max {
                run_max = neededTime[j];
            }
            j += 1;
        }

        ans += run_sum - run_max;
        i = j;
    }

    ans
}
