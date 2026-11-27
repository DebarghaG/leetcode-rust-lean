pub fn rearrange_characters(s: &[u8], target: &[u8]) -> i64 {
    let mut s_count: Vec<i64> = Vec::new();
    let mut target_count: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < 26 {
        s_count.push(0);
        target_count.push(0);
        i += 1;
    }

    i = 0;
    while i < s.len() {
        let idx = (s[i] - b'a') as usize;
        s_count[idx] = s_count[idx] + 1;
        i += 1;
    }

    i = 0;
    while i < target.len() {
        let idx = (target[i] - b'a') as usize;
        target_count[idx] = target_count[idx] + 1;
        i += 1;
    }

    let mut ans: i64 = 1000000;
    i = 0;
    while i < 26 {
        if target_count[i] > 0 {
            let possible = s_count[i] / target_count[i];
            if possible < ans {
                ans = possible;
            }
        }
        i += 1;
    }

    ans
}
