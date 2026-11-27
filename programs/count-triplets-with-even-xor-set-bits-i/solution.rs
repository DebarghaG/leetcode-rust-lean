pub fn triplet_count(a: &[i64], b: &[i64], c: &[i64]) -> i64 {
    let mut even_a: i64 = 0;
    let mut odd_a: i64 = 0;
    let mut even_b: i64 = 0;
    let mut odd_b: i64 = 0;
    let mut even_c: i64 = 0;
    let mut odd_c: i64 = 0;

    let mut i: usize = 0;
    while i < a.len() {
        if set_bits_parity(a[i]) == 0 {
            even_a += 1;
        } else {
            odd_a += 1;
        }
        i += 1;
    }

    let mut j: usize = 0;
    while j < b.len() {
        if set_bits_parity(b[j]) == 0 {
            even_b += 1;
        } else {
            odd_b += 1;
        }
        j += 1;
    }

    let mut k: usize = 0;
    while k < c.len() {
        if set_bits_parity(c[k]) == 0 {
            even_c += 1;
        } else {
            odd_c += 1;
        }
        k += 1;
    }

    even_a * even_b * even_c
        + even_a * odd_b * odd_c
        + odd_a * even_b * odd_c
        + odd_a * odd_b * even_c
}

fn set_bits_parity(mut x: i64) -> i64 {
    let mut parity: i64 = 0;
    while x > 0 {
        if x % 2 == 1 {
            parity = 1 - parity;
        }
        x = x / 2;
    }
    parity
}
