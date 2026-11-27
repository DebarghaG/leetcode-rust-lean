pub fn knight_dialer(n: i64) -> i64 {
    let modulus: i64 = 1000000007;

    let mut a0: i64 = 1;
    let mut a1: i64 = 1;
    let mut a2: i64 = 1;
    let mut a3: i64 = 1;
    let mut a4: i64 = 1;
    let mut a5: i64 = 1;
    let mut a6: i64 = 1;
    let mut a7: i64 = 1;
    let mut a8: i64 = 1;
    let mut a9: i64 = 1;

    let mut step: i64 = 1;

    while step < n {
        let n0: i64 = (a4 + a6) % modulus;
        let n1: i64 = (a6 + a8) % modulus;
        let n2: i64 = (a7 + a9) % modulus;
        let n3: i64 = (a4 + a8) % modulus;
        let n4: i64 = (a0 + a3 + a9) % modulus;
        let n5: i64 = 0;
        let n6: i64 = (a0 + a1 + a7) % modulus;
        let n7: i64 = (a2 + a6) % modulus;
        let n8: i64 = (a1 + a3) % modulus;
        let n9: i64 = (a2 + a4) % modulus;

        a0 = n0;
        a1 = n1;
        a2 = n2;
        a3 = n3;
        a4 = n4;
        a5 = n5;
        a6 = n6;
        a7 = n7;
        a8 = n8;
        a9 = n9;

        step = step + 1;
    }

    let answer: i64 = (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9) % modulus;
    answer
}
