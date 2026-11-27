pub fn max_consecutive(bottom: i64, top: i64, special: &[i64]) -> i64 {
    let mut s: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < special.len() {
        s.push(special[i]);
        i += 1;
    }

    s.sort();
    let n = s.len();

    if n == 0 {
        return top - bottom + 1;
    }

    let mut ans: i64 = 0;

    let first_gap = s[0] - bottom;
    if first_gap > ans {
        ans = first_gap;
    }

    let mut j: usize = 1;
    while j < n {
        let gap = s[j] - s[j - 1] - 1;
        if gap > ans {
            ans = gap;
        }
        j += 1;
    }

    let last_gap = top - s[n - 1];
    if last_gap > ans {
        ans = last_gap;
    }

    ans
}
