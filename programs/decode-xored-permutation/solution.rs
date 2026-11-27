pub fn decode(encoded: &[i64]) -> Vec<i64> {
    let n: usize = encoded.len() + 1;

    let mut xor_all: i64 = 0;
    let mut i: usize = 1;
    while i <= n {
        xor_all = xor_all ^ (i as i64);
        i += 1;
    }

    let mut xor_odd: i64 = 0;
    let mut j: usize = 1;
    while j < encoded.len() {
        xor_odd = xor_odd ^ encoded[j];
        j += 2;
    }

    let first: i64 = xor_all ^ xor_odd;

    let mut out: Vec<i64> = Vec::new();
    out.push(first);

    let mut prev: i64 = first;
    let mut k: usize = 0;
    while k < encoded.len() {
        let next: i64 = prev ^ encoded[k];
        out.push(next);
        prev = next;
        k += 1;
    }

    out
}
