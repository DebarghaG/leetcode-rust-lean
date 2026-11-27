pub fn add_rungs(rungs: &[i64], dist: i64) -> i64 {
    let mut ans: i64 = 0;
    let mut prev: i64 = 0;
    let mut i: usize = 0;

    while i < rungs.len() {
        let cur: i64 = rungs[i];
        let gap: i64 = cur - prev;

        if gap > dist {
            ans = ans + (gap - 1) / dist;
        }

        prev = cur;
        i = i + 1;
    }

    ans
}
