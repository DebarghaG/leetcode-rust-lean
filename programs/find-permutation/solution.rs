pub fn find_permutation(s: &[u8]) -> Vec<i64> {
    let m = s.len();
    let n = m + 1;

    let mut res: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    let mut cur: i64 = 1;

    while idx < n {
        res.push(cur);
        cur = cur + 1;
        idx = idx + 1;
    }

    let mut i: usize = 0;
    while i < m {
        if s[i] == b'D' {
            let mut j: usize = i;
            while j < m && s[j] == b'D' {
                j = j + 1;
            }

            let mut left: usize = i;
            let mut right: usize = j;

            while left < right {
                let tmp = res[left];
                res[left] = res[right];
                res[right] = tmp;

                left = left + 1;
                right = right - 1;
            }

            i = j;
        } else {
            i = i + 1;
        }
    }

    res
}
