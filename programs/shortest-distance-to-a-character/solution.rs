pub fn shortest_to_char(s: &[u8], c: &[u8]) -> Vec<i64> {
    let n = s.len();
    let target = c[0];

    let mut ans: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        ans.push(1000000000);
        k += 1;
    }

    let mut last: usize = n;
    let mut i: usize = 0;
    while i < n {
        if s[i] == target {
            last = i;
        }
        if last != n {
            ans[i] = (i - last) as i64;
        }
        i += 1;
    }

    let mut last_right: usize = n;
    let mut j: usize = n;
    while j > 0 {
        j -= 1;
        if s[j] == target {
            last_right = j;
        }
        if last_right != n {
            let d: i64 = (last_right - j) as i64;
            if d < ans[j] {
                ans[j] = d;
            }
        }
    }

    ans
}
