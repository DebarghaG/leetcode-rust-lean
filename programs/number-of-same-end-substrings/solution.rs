pub fn same_end_substring_count(s: &[u8], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = s.len();

    // pref[c][i] = number of occurrences of byte ('a' + c) in s[0..i]
    let mut pref: Vec<Vec<i64>> = Vec::new();
    let mut c: usize = 0;
    while c < 26 {
        let target: u8 = b'a' + (c as u8);
        let mut row: Vec<i64> = Vec::new();

        let mut j: usize = 0;
        while j <= n {
            row.push(0);
            j += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let add: i64 = if s[i] == target { 1 } else { 0 };
            row[i + 1] = row[i] + add;
            i += 1;
        }

        pref.push(row);
        c += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut qi: usize = 0;

    while qi < queries.len() {
        let q = &queries[qi];
        let l: usize = q[0] as usize;
        let r: usize = q[1] as usize;

        let mut total: i64 = 0;
        let mut ch: usize = 0;

        while ch < 26 {
            let count: i64 = pref[ch][r + 1] - pref[ch][l];
            total = total + count * (count + 1) / 2;
            ch += 1;
        }

        ans.push(total);
        qi += 1;
    }

    ans
}
