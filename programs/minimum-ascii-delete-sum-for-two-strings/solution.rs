pub fn minimum_delete_sum(s1: &[u8], s2: &[u8]) -> i64 {
    let m = s1.len();
    let n = s2.len();

    let mut prev: Vec<i64> = Vec::new();
    prev.push(0);

    let mut j: usize = 1;
    while j <= n {
        prev.push(prev[j - 1] + (s2[j - 1] as i64));
        j += 1;
    }

    let mut i: usize = 1;
    while i <= m {
        let mut curr: Vec<i64> = Vec::new();
        curr.push(prev[0] + (s1[i - 1] as i64));

        j = 1;
        while j <= n {
            if s1[i - 1] == s2[j - 1] {
                curr.push(prev[j - 1]);
            } else {
                let delete_from_s1 = prev[j] + (s1[i - 1] as i64);
                let delete_from_s2 = curr[j - 1] + (s2[j - 1] as i64);

                if delete_from_s1 < delete_from_s2 {
                    curr.push(delete_from_s1);
                } else {
                    curr.push(delete_from_s2);
                }
            }
            j += 1;
        }

        prev = curr;
        i += 1;
    }

    prev[n]
}
