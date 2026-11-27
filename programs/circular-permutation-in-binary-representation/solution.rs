pub fn circular_permutation(n: i64, start: i64) -> Vec<i64> {
    // size = 2^n
    let mut size: i64 = 1;
    let mut t: i64 = 0;
    while t < n {
        size = size * 2;
        t += 1;
    }

    // Compute k, the index in the Gray-code sequence whose value is `start`.
    // Inverse Gray code: k = start ^ (start>>1) ^ (start>>2) ^ ... ^ (start>>(n-1)).
    let mut k: i64 = start;
    let mut sh: i64 = 1;
    while sh < n {
        k = k ^ (start >> sh);
        sh += 1;
    }

    let mut out: Vec<i64> = Vec::new();

    // Emit Gray-code values for indices k, k+1, ..., size-1.
    let mut a: i64 = k;
    while a < size {
        let g: i64 = a ^ (a >> 1);
        out.push(g);
        a += 1;
    }

    // Emit Gray-code values for indices 0, 1, ..., k-1.
    let mut b: i64 = 0;
    while b < k {
        let g: i64 = b ^ (b >> 1);
        out.push(g);
        b += 1;
    }

    out
}
