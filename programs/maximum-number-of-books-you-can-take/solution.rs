pub fn maximum_books(books: &[i64]) -> i64 {
    let n: usize = books.len();
    let mut dp: Vec<i64> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    let mut ans: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let bi: i64 = books[i];
        let i_val: i64 = i as i64;
        let ci: i64 = bi - i_val;

        while stack.len() > 0 {
            let top: usize = stack[stack.len() - 1];
            let ctop: i64 = books[top] - (top as i64);
            if ctop >= ci {
                stack.pop();
            } else {
                break;
            }
        }

        let val: i64;

        if stack.len() == 0 {
            let mut len: i64 = i_val + 1;
            if bi < len {
                len = bi;
            }

            if len <= 0 {
                val = 0;
            } else {
                val = (len * (2 * bi - len + 1)) / 2;
            }
        } else {
            let j: usize = stack[stack.len() - 1];
            let len: i64 = (i - j) as i64;
            let last: i64 = bi - len + 1;
            let sum: i64 = (len * (bi + last)) / 2;
            val = dp[j] + sum;
        }

        dp.push(val);
        if val > ans {
            ans = val;
        }

        stack.push(i);
        i += 1;
    }

    ans
}
