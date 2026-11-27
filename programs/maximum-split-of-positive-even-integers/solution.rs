pub fn maximum_even_split(finalSum: i64) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();

    if finalSum <= 0 {
        return ans;
    }
    if finalSum % 2 != 0 {
        return ans;
    }

    let n: i64 = finalSum / 2;

    let mut sum: i64 = 0;
    let mut next: i64 = 1;
    let mut m: i64 = 0;

    while sum + next <= n {
        sum = sum + next;
        m = m + 1;
        next = next + 1;
    }

    let mut i: i64 = 1;
    while i < m {
        ans.push(2 * i);
        i = i + 1;
    }

    if m > 0 {
        let last_half: i64 = n - (sum - m);
        ans.push(2 * last_half);
    }

    ans
}
