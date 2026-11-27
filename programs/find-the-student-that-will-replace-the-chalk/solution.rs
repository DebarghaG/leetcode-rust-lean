pub fn chalk_replacer(chalk: &[i64], k: i64) -> i64 {
    let n = chalk.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += chalk[i];
        i += 1;
    }

    let mut remaining: i64 = k % total;

    i = 0;
    let mut answer: i64 = 0;
    while i < n {
        if remaining < chalk[i] {
            return answer;
        }
        remaining -= chalk[i];
        i += 1;
        answer += 1;
    }

    0
}
