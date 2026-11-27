pub fn num_matching_subseq(s: &[u8], words: &[Vec<u8>]) -> i64 {
    let n = s.len();
    let m = words.len();
    let mut ans: i64 = 0;
    let mut k: usize = 0;

    while k < m {
        let w = &words[k];
        let wl = w.len();

        let mut i: usize = 0;
        let mut j: usize = 0;

        while i < n && j < wl {
            if s[i] == w[j] {
                j = j + 1;
            }
            i = i + 1;
        }

        if j == wl {
            ans = ans + 1;
        }

        k = k + 1;
    }

    ans
}
