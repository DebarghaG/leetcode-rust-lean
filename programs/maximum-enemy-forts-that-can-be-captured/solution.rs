pub fn capture_forts(forts: &[i64]) -> i64 {
    let n = forts.len();
    let mut ans: i64 = 0;
    let mut g: i64 = 0; // previous non-zero value (1 or -1); 0 means none yet
    let mut c: i64 = 0; // number of zeros seen since the previous non-zero
    let mut i: usize = 0;

    while i < n {
        let v = forts[i];
        let v2 = v * v;          // 1 if v != 0, else 0
        let nz = 1 - v2;         // 1 if v == 0, else 0
        let prod = g * v;        // -1 if opposite signs, 0 if either is zero, 1 if same
        let cand = (0 - prod) * c; // == c when opposite (prod == -1); <= 0 otherwise

        if cand > ans {
            ans = cand;
        }

        // Unconditional straight-line state updates.
        g = v + nz * g;          // set to v when v != 0, else keep g
        c = nz * (c + 1);        // reset to 0 when v != 0, else increment

        i = i + 1;
    }

    ans
}
