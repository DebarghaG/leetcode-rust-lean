pub fn can_make_pali_queries(s: &[u8], queries: &[Vec<i64>]) -> Vec<bool> {
    let n = s.len();

    let mut pref: Vec<Vec<i64>> = Vec::new();
    let mut initial: Vec<i64> = Vec::new();
    let mut c = 0usize;
    while c < 26 {
        initial.push(0i64);
        c += 1;
    }
    pref.push(initial);

    let mut i = 0usize;
    while i < n {
        let mut curr: Vec<i64> = Vec::new();
        let mut c2 = 0usize;
        while c2 < 26 {
            curr.push(pref[i][c2]);
            c2 += 1;
        }

        let letter = (s[i] - b'a') as usize;
        curr[letter] += 1i64;
        pref.push(curr);

        i += 1;
    }

    let mut ans: Vec<bool> = Vec::new();
    let qn = queries.len();
    let mut q = 0usize;

    while q < qn {
        let left = queries[q][0] as usize;
        let right = queries[q][1] as usize;
        let k = queries[q][2];

        let mut odd: i64 = 0;
        let mut c3 = 0usize;
        while c3 < 26 {
            let cnt = pref[right + 1][c3] - pref[left][c3];
            if cnt % 2 == 1 {
                odd += 1;
            }
            c3 += 1;
        }

        ans.push(odd / 2 <= k);
        q += 1;
    }

    ans
}
