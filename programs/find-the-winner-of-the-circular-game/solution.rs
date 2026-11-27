pub fn find_the_winner(n: i64, k: i64) -> i64 {
    let mut ans: i64 = 0;
    let mut i: i64 = 2;

    while i <= n {
        ans = (ans + k) % i;
        i = i + 1;
    }

    ans + 1
}
