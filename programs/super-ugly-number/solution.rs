pub fn nth_super_ugly_number(n: i64, primes: &[i64]) -> i64 {
    let n_usize: usize = n as usize;
    let k: usize = primes.len();

    let mut ugly: Vec<i64> = Vec::new();
    ugly.push(1);

    let mut idx: Vec<usize> = Vec::new();
    let mut j: usize = 0;
    while j < k {
        idx.push(0);
        j = j + 1;
    }

    let mut i: usize = 1;
    while i < n_usize {
        let mut next_val: i64 = 9223372036854775807;

        j = 0;
        while j < k {
            let cand = primes[j] * ugly[idx[j]];
            if cand < next_val {
                next_val = cand;
            }
            j = j + 1;
        }

        ugly.push(next_val);

        j = 0;
        while j < k {
            let cand = primes[j] * ugly[idx[j]];
            if cand == next_val {
                idx[j] = idx[j] + 1;
            }
            j = j + 1;
        }

        i = i + 1;
    }

    ugly[n_usize - 1]
}
