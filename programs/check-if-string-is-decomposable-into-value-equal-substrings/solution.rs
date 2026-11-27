pub fn is_decomposable(s: &[u8]) -> bool {
    let n = s.len();

    let mut have_two: bool = false;
    let mut ok: bool = true;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n && s[j] == s[i] {
            j += 1;
        }

        let run_len: usize = j - i;
        let rem: usize = run_len % 3;

        if rem == 1 {
            ok = false;
        } else if rem == 2 {
            if have_two {
                ok = false;
            } else {
                have_two = true;
            }
        }

        i = j;
    }

    ok && have_two
}
