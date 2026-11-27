pub fn find_min_fibonacci_numbers(k: i64) -> i64 {
    if k <= 0 {
        return 0;
    }

    let mut fib: Vec<i64> = Vec::new();
    fib.push(1);
    fib.push(2);

    let mut next: i64 = 3;
    while next <= k {
        fib.push(next);
        let n = fib.len();
        next = fib[n - 1] + fib[n - 2];
    }

    let mut rem: i64 = k;
    let mut ans: i64 = 0;

    while rem > 0 {
        let mut j: usize = fib.len();
        let mut chosen: i64 = 1;

        while j > 0 {
            j = j - 1;
            if fib[j] <= rem && fib[j] > chosen {
                chosen = fib[j];
            }
        }

        rem = rem - chosen;
        ans = ans + 1;
    }

    ans
}
